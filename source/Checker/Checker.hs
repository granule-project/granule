{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Checker.Checker where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Maybe
import Data.SBV hiding (kindOf)

import Checker.Coeffects
import Checker.Constraints
import Checker.Kinds
import Checker.Monad
import Checker.Patterns
import Checker.Predicates
import Checker.Primitives
import Checker.Substitutions
import Checker.Types
import Context
import Syntax.Expr
import Syntax.Pretty
import Utils


data CheckerResult = Failed | Ok deriving (Eq, Show)

-- Checking (top-level)
check :: (?globals :: Globals )
      => [Def]        -- List of definitions
      -> IO CheckerResult
check defs = do
    -- Get the types of all definitions (assume that they are correct for
    -- the purposes of (mutually)recursive calls).

    -- Kind check all the type signatures
    let checkKinds = mapM (\(Def s _ _ _ tys) -> kindCheck s tys) defs

    -- Build a computation which checks all the defs (in order)...
    let defCtxt = map (\(Def _ var _ _ tys) -> (var, tys)) defs
    let checkedDefs = do
          status <- runMaybeT checkKinds
          case status of
            Nothing -> return [Nothing]
            Just _  -> -- Now check the definition
               mapM (checkDef defCtxt) defs

    -- ... and evaluate the computation with initial state
    results <- evalChecker initState checkedDefs

    -- If all definitions type checked, then the whole file type checkers
    if all isJust results
      then return Ok
      else return Failed

checkDef :: (?globals :: Globals )
         => Ctxt TypeScheme  -- context of top-level definitions
         -> Def              -- definition
         -> Checker (Maybe (Ctxt Assumption))
checkDef defCtxt (Def s defName expr pats (Forall _ foralls ty)) = do
    ctxt <- runMaybeT $ do
      modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) foralls})

      ctxt <- case (ty, pats) of
        (FunTy _ _, ps@(_:_)) -> do

          -- Type the pattern matching
          (patternGam, ty') <- ctxtFromTypedPatterns s ty ps
          -- Check the body in the context given by the pattern matching
          (outGam, _) <- checkExpr defCtxt patternGam Positive True ty' expr
          -- Check that the outgoing context is a subgrading of the incoming
          leqCtxt s outGam patternGam

          -- Check linear use
          case checkLinearity patternGam outGam of
                [] -> return outGam
                xs -> illLinearityMismatch s xs

        (tau, []) -> checkExpr defCtxt [] Positive True tau expr >>= (return . fst)
        _         -> halt $ GenericError (Just s) "Expecting a function type"

      -- Use an SMT solver to solve the generated constraints
      checkerState <- get
      let predStack = predicateStack checkerState
      debugM "Solver predicate" $ pretty (Conj predStack)

      solved <- solveConstraints (Conj predStack) s defName
      if solved
        then return ctxt
        else halt $ GenericError (Just s) "Constraints violated"

    -- Erase the solver predicate between definitions
    modify (\st -> st { predicateStack = [], tyVarContext = [], kVarContext = [] })
    return ctxt

data Polarity = Positive | Negative deriving Show


flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

-- Type check an expression

--  `checkExpr defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in context `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: (?globals :: Globals )
          => Ctxt TypeScheme   -- context of top-level definitions
          -> Ctxt Assumption   -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Bool             -- whether we are top-level or not
          -> Type             -- type
          -> Expr             -- expression
          -> MaybeT Checker (Ctxt Assumption, Ctxt Type)

-- Checking of constants

checkExpr _ _ _ _ (TyCon "Int") (Val _ (NumInt _)) = return ([], [])
  -- Automatically upcast integers to floats
checkExpr _ _ _ _ (TyCon "Float") (Val _ (NumInt _)) = return ([], [])
checkExpr _ _ _ _ (TyCon "Float") (Val _ (NumFloat _)) = return ([], [])

checkExpr defs gam pol _ (FunTy sig tau) (Val s (Abs x t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here
  (tau', subst1) <- case t of
    Nothing -> return (tau, [])
    Just t' -> do
      (eqT, unifiedType, subst) <- equalTypes s sig t'
      unless eqT (halt $ GenericError (Just s) $ pretty sig ++ " not equal to " ++ pretty t')
      return (tau, subst)

  -- Extend the context with the variable 'x' and its type
  gamE <- extCtxt s gam x (Linear sig)
  -- Check the body in the extended context
  (gam', subst2) <- checkExpr defs gamE pol False tau' e
  -- Linearity check, variables must be used exactly once
  case lookup x gam' of
    Nothing -> illLinearityMismatch s [LinearNotUsed x]
    Just _  -> return (eraseVar gam' x, subst1 ++ subst2)

-- Application special case for built-in 'scale'
checkExpr defs gam pol topLevel tau
          (App s (App _ (Val _ (Var v)) (Val _ (NumFloat x))) e) | internalName v == "scale" = do
    equalTypes s (TyCon "Float") tau
    checkExpr defs gam pol topLevel (Box (CFloat (toRational x)) (TyCon "Float")) e

-- Application
checkExpr defs gam pol topLevel tau (App s e1 e2) = do
    (argTy, gam2) <- synthExpr defs gam pol e2
    (gam1, subst) <- checkExpr defs gam (flipPol pol) topLevel (FunTy argTy tau) e1
    gam' <- ctxPlus s gam1 gam2
    return (gam', subst)

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr defs gam pol _ (Box demand tau) (Val s (Promote e)) = do
  gamF    <- discToFreshVarsIn s (freeVars e) gam demand
  (gam', subst) <- checkExpr defs gamF pol False tau e
  let gam'' = multAll (freeVars e) demand gam'
  return (gam'', subst)

checkExpr defs gam pol _ tau (Case s guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam) <- synthExpr defs gam pol guardExpr

  -- Check each of the branches
  branchCtxtsAndSubst <-
    forM cases $ \(pat_i, e_i) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst) <- ctxtFromTypedPattern s guardTy pat_i

      -- Checking the case body
      newConjunct
      -- Specialise the return type and the incoming environment using the
      -- pattern-match-generated type substitution
      let tau' = substType subst tau
      (specialisedGam, unspecialisedGam) <- substCtxt subst gam

      let checkGam = specialisedGam ++ unspecialisedGam ++ patternGam
      (localGam, subst') <- checkExpr defs checkGam pol False tau' e_i

      leqCtxt s localGam checkGam

      -- Check linear use in anything Linear
      case checkLinearity patternGam localGam of
        -- Return the resulting computed context, without any of
        -- the variable bound in the pattern of this branch
        [] -> do
           -- The current local environment should be subsumed by the
           -- shared context
           -- Conclude the implication
           concludeImplication eVars
           state <- get

           -- The resulting context has the shared part removed
           let branchCtxt = (localGam `subtractCtxt` patternGam) `subtractCtxt` specialisedGam

           return (branchCtxt, subst')

        -- Anything that was bound in the pattern but not used correctly
        xs -> illLinearityMismatch s xs

  -- Find the upper-bound contexts
  let (branchCtxts, substs) = unzip branchCtxtsAndSubst
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  -- Contract the outgoing context of the guard and the branches (joined)
  g <- ctxPlus s branchesGam guardGam

  return (g, concat substs)

-- All other expressions must be checked using synthesis
checkExpr defs gam pol topLevel tau e = do
  (tau', gam') <- synthExpr defs gam pol e
  (tyEq, _, subst) <-
    case pol of
      Positive -> do
        debugM "+ Compare for equality " $ pretty tau' ++ " = " ++ pretty tau
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then equalTypes (getSpan e) tau' tau
          else lEqualTypes (getSpan e) tau' tau

      -- i.e., this check is from a synth
      Negative -> do
        debugM "- Compare for equality " $ pretty tau ++ " = " ++ pretty tau'
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then equalTypes (getSpan e) tau tau'
          else lEqualTypes (getSpan e) tau tau'

  if tyEq
    then return (gam', subst)
    else do
      halt $ GenericError (Just $ getSpan e)
          $ "Expected '" ++ pretty tau ++ "' but got '" ++ pretty tau' ++ "'"

-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: (?globals :: Globals)
          => Ctxt TypeScheme -- ^ Context of top-level definitions
          -> Ctxt Assumption   -- ^ Local typing context
          -> Polarity       -- ^ Polarity of subgrading
          -> Expr           -- ^ Expression
          -> MaybeT Checker (Type, Ctxt Assumption)

-- Constants (numbers)
synthExpr _ _ _ (Val _ (NumInt _))  = return (TyCon "Int", [])
synthExpr _ _ _ (Val _ (NumFloat _)) = return (TyCon "Float", [])

-- Polymorphic list constructors
synthExpr _ _ _ (Val _ (Constr "Nil" [])) = do
  elementVarName <- freshVar "a"
  let elementVar = mkId elementVarName
  modify (\st -> st { tyVarContext = (elementVar, (KType, InstanceQ)) : tyVarContext st })
  return (TyApp (TyApp (TyCon "List") (TyInt 0)) (TyVar elementVar), [])

synthExpr _ _ _ (Val s (Constr "Cons" [])) = do
    let kind = CConstr "Nat="
    sizeVarArg <- freshCoeffectVar (mkId "n") kind
    sizeVarRes <- freshCoeffectVar (mkId "m") kind
    elementVarName <- freshVar "a"
    let elementVar = mkId elementVarName
    modify (\st -> st { tyVarContext = (elementVar, (KType, InstanceQ)) : tyVarContext st })
    -- Add a constraint
    -- m ~ n + 1
    addConstraint $ Eq s (CVar sizeVarRes)
                         (CPlus (CNat Discrete 1) (CVar sizeVarArg)) kind
    -- Cons : a -> List n a -> List m a
    return (FunTy
             (TyVar elementVar)
             (FunTy (list elementVar (TyVar sizeVarArg))
                    (list elementVar (TyVar sizeVarRes))),
                    [])
  where
    list elementVar n = TyApp (TyApp (TyCon "List") n) (TyVar $ elementVar)

-- Nat constructors
synthExpr _ _ _ (Val _ (Constr "Z" [])) = do
  return (TyApp (TyCon "N") (TyInt 0), [])

synthExpr _ _ _ (Val s (Constr "S" [])) = do
    let kind = CConstr "Nat="
    sizeVarArg <- freshCoeffectVar (mkId "n") kind
    sizeVarRes <- freshCoeffectVar (mkId "m") kind
    -- Add a constraint
    -- m ~ n + 1
    addConstraint $ Eq s (CVar sizeVarRes)
                         (CPlus (CNat Discrete 1) (CVar sizeVarArg)) kind
    -- S : Nat n -> Nat (n + 1)
    return (FunTy (nat (TyVar sizeVarArg))
                  (nat (TyVar sizeVarRes)), [])
  where
    nat n = TyApp (TyCon "N") n


-- Constructors (only supports nullary constructors)
synthExpr _ _ _ (Val s (Constr name [])) = do
  case lookup name dataConstructors of
    Just (Forall _ [] t) -> return (t, [])
    _ -> halt $ UnboundVariableError (Just s) $ "Data constructor " ++ name

-- Case
synthExpr defs gam pol (Case s guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam) <- synthExpr defs gam pol guardExpr
  -- then synthesise the types of the branches
  branchTysAndCtxts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, _) <- ctxtFromTypedPattern s ty pati
      newConjunct
      ---
      (tyCase, localGam) <- synthExpr defs (gam ++ patternGam) pol ei
      concludeImplication eVars
      -- Check linear use in anything Linear
      case checkLinearity patternGam localGam of
         -- Return the resulting computed context, without any of
         -- the variable bound in the pattern of this branch
         [] -> return (tyCase, localGam `subtractCtxt` patternGam)
         xs -> illLinearityMismatch s xs

  let (branchTys, branchCtxts) = unzip branchTysAndCtxts
  let branchTysAndSpans = zip branchTys (map (getSpan . snd) cases)
  -- Finds the upper-bound return type between all branches
  eqTypes <- foldM (\ty2 (ty1, sp) -> joinTypes sp ty1 ty2)
                   (head branchTys)
                   (tail branchTysAndSpans)

  -- Find the upper-bound type on the return contexts
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxPlus s branchesGam guardGam

  return (eqTypes, gamNew)

-- Diamond cut
synthExpr defs gam pol (LetDiamond s var ty e1 e2) = do
  gam'        <- extCtxt s gam var (Linear ty)
  (tau, gam1) <- synthExpr defs gam' pol e2
  case tau of
    Diamond ef2 tau' -> do
       (sig, gam2) <- synthExpr defs gam pol e1
       case sig of
         Diamond ef1 ty' | ty == ty' -> do
             gamNew <- ctxPlus s gam1 gam2
             return (Diamond (ef1 ++ ef2) tau', gamNew)
         t -> do
          halt $ GenericError (Just s)
               $ "Expected '" ++ pretty ty ++ "' but inferred '"
               ++ pretty t ++ "' in body of let<>"
    t -> do
      halt $ GenericError (Just s)
           $ "Expected '" ++ pretty ty
           ++ "' in subjet of let <-, but inferred '" ++ pretty t ++ "'"

-- Variables
synthExpr defs gam _ (Val s (Var x)) = do
   -- Try the local context
   case lookup x gam of
     Nothing ->
       -- Try definitions in scope
       case lookup x (defs ++ builtins) of
         Just tyScheme  -> do
           ty' <- freshPolymorphicInstance tyScheme
           return (ty', [])
         -- Couldn't find it
         Nothing  -> halt $ UnboundVariableError (Just s) $ pretty x
                              ++ (if debugging ?globals then
                                  (" { looking for " ++ pretty x
                                  ++ " in context " ++ pretty gam
                                  ++ "}")
                                 else "")
     -- In the local context
     Just (Linear ty)       -> return (ty, [(x, Linear ty)])
     Just (Discharged ty c) -> do
       k <- inferCoeffectType s c
       return (ty, [(x, Discharged ty (COne k))])

-- Specialised application for scale
synthExpr defs gam pol
      (App _ (Val _ (Var v)) (Val _ (NumFloat r))) | internalName v == "scale" = do
  let float = (TyCon "Float")
  return $ (FunTy (Box (CFloat (toRational r)) float) float, [])

-- Application
synthExpr defs gam pol (App s e e') = do

    (fTy, gam1) <- synthExpr defs gam pol e
    case fTy of
      -- Got a function type for the left-hand side of application
      (FunTy sig tau) -> do
         (gam2, subst) <- checkExpr defs gam pol False sig e'
         gamNew <- ctxPlus s gam1 gam2
         return (substType subst tau, gamNew)

      -- Not a function type
      t -> do
        halt $ GenericError (Just s) $ "Left-hand side of application is not a function"
                   ++ " but has type '" ++ pretty t ++ "'"

-- Promotion
synthExpr defs gam pol (Val s (Promote e)) = do
   debugM "Synthing a promotion of " $ pretty e

   -- Create a fresh kind variable for this coeffect
   vark <- freshVar $ "kprom_" ++ [head (pretty e)]

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshCoeffectVar (mkId $ "prom_" ++ pretty e) (CPoly $ mkId vark)

   gamF <- discToFreshVarsIn s (freeVars e) gam (CVar var)

   (t, gam') <- synthExpr defs gamF pol e

   return (Box (CVar var) t, multAll (freeVars e) (CVar var) gam')

-- Letbox
synthExpr defs gam pol (LetBox s var t e1 e2) = do

    -- Create a fresh kind variable for this coeffect
    ckvar <- freshVar ("binderk_" ++ sourceName var)
    let kind = CPoly $ mkId ckvar

    -- Update coeffect-kind context
    cvar <- freshCoeffectVar (mkId $ "binder_" ++ sourceName var) kind

    -- Extend the context with cvar
    gam' <- extCtxt s gam var (Discharged t (CVar cvar))

    (tau, gam2) <- synthExpr defs gam' pol e2

    (demand, t'') <-
      case lookup var gam2 of
        Just (Discharged t' demand) -> do
             (eqT, unifiedType, _) <- equalTypes s t' t
             if eqT then do
                debugM "synthExpr LetBox" $ "Demand for " ++ pretty var ++ " = " ++ pretty demand
                return (demand, unifiedType)
              else
                halt $ GenericError (Just s) $ "An explicit signature is given "
                         ++ pretty var
                         ++ " : '" ++ pretty t
                         ++ "' but the actual type was '" ++ pretty t' ++ "'"
        _ -> do
          -- If there is no explicit demand for the variable
          -- then this means it is not used
          -- Therefore c ~ 0
          addConstraint (Eq s (CVar cvar) (CZero kind) kind)
          return (CZero kind, t)

    (gam1, _) <- checkExpr defs gam (flipPol pol) False (Box demand t'') e1
    gamNew <- ctxPlus s gam1 gam2
    return (tau, gamNew)

-- BinOp
synthExpr defs gam pol (Binop s op e1 e2) = do
    (t1, gam1) <- synthExpr defs gam pol e1
    (t2, gam2) <- synthExpr defs gam pol e2
    -- Look through the list of operators (of which there might be
    -- multiple matching operators)
    case lookupMany op binaryOperators of
      [] -> halt $ UnboundVariableError (Just s) $ "Binary operator " ++ op
      ops -> do
        returnType <- selectFirstByType t1 t2 ops
        gamOut <- ctxPlus s gam1 gam2
        return (returnType, gamOut)

  where
    -- No matching type were found (meaning there is a type error)
    selectFirstByType t1 t2 [] =
      halt $ GenericError (Just s) $ "Could not resolve operator " ++ op ++ " at type: "
         ++ pretty (FunTy t1 (FunTy t2 (TyVar $ mkId "...")))

    selectFirstByType t1 t2 ((FunTy opt1 (FunTy opt2 resultTy)):ops) = do
      -- Attempt to use this typing
      (result, local) <- localChecking $ do
         (eq1, _, _) <- equalTypes s t1 opt1
         (eq2, _, _) <- equalTypes s t2 opt2
         return (eq1 && eq2)
      -- If successful then return this local computation
      case result of
        Just True -> local >> return resultTy
        _         -> selectFirstByType t1 t2 ops

    selectFirstByType t1 t2 (_:ops) = selectFirstByType t1 t2 ops


-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s (Abs x (Just sig) e)) = do
  gam' <- extCtxt s gam x (Linear sig)
  (tau, gam'') <- synthExpr defs gam' pol e
  return (FunTy sig tau, gam'')

-- Pair
synthExpr defs gam pol (Val s (Pair e1 e2)) = do
  (t1, gam1) <- synthExpr defs gam pol e1
  (t2, gam2) <- synthExpr defs gam pol e2
  gam' <- ctxPlus s gam1 gam2
  return (PairTy t1 t2, gam')

synthExpr _ _ _ e =
  halt $ GenericError (Just $ getSpan e) "Type cannot be calculated here; try adding more type signatures."


solveConstraints :: (?globals :: Globals) => Pred -> Span -> Id -> MaybeT Checker Bool
solveConstraints predicate s defName = do
  -- Get the coeffect kind context and constraints
  checkerState <- get
  let ctxtCk  = tyVarContext checkerState
  let ctxtCkVar = kVarContext checkerState
  let coeffectVars = justCoeffectTypesConverted ctxtCk
  let coeffectKVars = justCoeffectTypesConvertedVars ctxtCkVar

  let (sbvTheorem, _, unsats) = compileToSBV predicate coeffectVars coeffectKVars

  thmRes <- liftIO . prove $ sbvTheorem

  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) ->
        halt $ CheckerError Nothing $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModelAssignment thmRes of
               -- Main 'Falsifiable' result
               Right (False, assg :: [ Integer ] ) -> do
                   -- Show any trivial inequalities
                   mapM_ (\c -> halt $ GradingError (Just $ getSpan c) (pretty . Neg $ c)) unsats
                   -- Show fatal error, with prover result
                   {-
                   negated <- liftIO . sat $ sbvSatTheorem
                   print $ show $ getModelDictionary negated
                   case (getModelAssignment negated) of
                     Right (_, assg :: [Integer]) -> do
                       print $ show assg
                     Left msg -> print $ show msg
                   -}
                   halt $ GenericError (Just s) $ "Definition '" ++ pretty defName ++ "' is " ++ show thmRes

               Right (True, _) ->
                   halt $ GenericError (Just s) $ "Definition '" ++ pretty defName ++ "' returned probable model."

               Left str        ->
                   halt $ GenericError (Just s) $ "Definition '" ++ pretty defName ++ " had a solver fail: " ++ str

           else return True
  where
    justCoeffectTypesConverted = mapMaybe convert
      where
       convert (var, (KConstr constr, q)) =
           case lookup constr typeLevelConstructors of
             Just KCoeffect -> Just (var, (CConstr constr, q))
             _         -> Nothing
       -- TODO: currently all poly variables are treated as kind 'Coeffect'
       -- but this need not be the case, so this can be generalised
       convert (var, (KPoly constr, q)) = Just (var, (CPoly constr, q))
       convert _ = Nothing
    justCoeffectTypesConvertedVars =
       stripQuantifiers . justCoeffectTypesConverted . map (\(var, k) -> (var, (k, ForallQ)))

leqCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker ()
leqCtxt s ctxt1 ctxt2 = do
    let ctxt  = ctxt1 `intersectCtxts` ctxt2
        ctxt' = ctxt2 `intersectCtxts` ctxt1
    zipWithM_ (leqAssumption s) ctxt ctxt'

{- | Take the least-upper bound of two contexts.
     If one context contains a linear variable that is not present in
    the other, then the resulting context will not have this linear variable -}
joinCtxts :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
joinCtxts s ctxt1 ctxt2 = do
    -- All the type assumptions from ctxt1 whose variables appear in ctxt2
    -- and weaken all others
    ctxt  <- intersectCtxtsWithWeaken s ctxt1 ctxt2
    -- All the type assumptions from ctxt2 whose variables appear in ctxt1
    -- and weaken all others
    ctxt' <- intersectCtxtsWithWeaken s ctxt2 ctxt1

    -- Make an context with fresh coeffect variables for all
    -- the variables which are in both ctxt1 and ctxt2...
    varCtxt <- freshVarsIn s (map fst ctxt) ctxt

    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in ctxt and ctxt'
    zipWithM_ (leqAssumption s) ctxt varCtxt
    zipWithM_ (leqAssumption s) ctxt' varCtxt
    -- Return the common upper-bound context of ctxt1 and ctxt2
    return varCtxt

{- |  intersect contexts and weaken anything not appear in both
        relative to the left context (this is not commutative) -}
intersectCtxtsWithWeaken :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
intersectCtxtsWithWeaken s a b = do
   let intersected = intersectCtxts a b
   -- All the things that were not shared
   let remaining   = b `subtractCtxt` intersected
   let leftRemaining = a `subtractCtxt` intersected
   weakenedRemaining <- mapM weaken remaining
   let newCtxt = intersected ++ filter isNonLinearAssumption (weakenedRemaining ++ leftRemaining)
   return . normaliseCtxt $ newCtxt
  where
   isNonLinearAssumption :: (Id, Assumption) -> Bool
   isNonLinearAssumption (_, Discharged _ _) = True
   isNonLinearAssumption _                   = False

   weaken :: (Id, Assumption) -> MaybeT Checker (Id, Assumption)
   weaken (var, Linear t) =
       return (var, Linear t)
   weaken (var, Discharged t c) = do
       kind <- inferCoeffectType s c
       return (var, Discharged t (CZero kind))

{- | Given an input context and output context, check the usage of
     variables in the output, returning a list of usage mismatch
     information if, e.g., a variable is bound linearly in the input but is not
     used in the output, or is discharged in the output -}
checkLinearity :: Ctxt Assumption -> Ctxt Assumption -> [LinearityMismatch]
checkLinearity [] _ = []
checkLinearity ((v, Linear _):inCtxt) outCtxt =
  case lookup v outCtxt of
    -- Good: linear variable was used
    Just Linear{} -> checkLinearity inCtxt outCtxt
    -- Bad: linear variable was discharged (boxed var but binder not unboxed)
    Just Discharged{} -> LinearUsedNonLinearly v : checkLinearity inCtxt outCtxt
    Nothing -> LinearNotUsed v : checkLinearity inCtxt outCtxt

checkLinearity ((_, Discharged{}):inCtxt) outCtxt =
  -- Discharged things can be discarded, so it doesn't matter what
  -- happens with them
  checkLinearity inCtxt outCtxt


leqAssumption :: (?globals :: Globals) => Span -> (Id, Assumption) -> (Id, Assumption)
  -> MaybeT Checker ()

-- Linear assumptions ignored
leqAssumption _ (_, Linear _)        (_, Linear _) = return ()

-- Discharged coeffect assumptions
leqAssumption s (_, Discharged _ c1) (_, Discharged _ c2) = do
  kind <- mguCoeffectTypes s c1 c2
  addConstraint (Leq s c1 c2 kind)

leqAssumption s x y =
  halt $ GenericError (Just s) $ "Can't unify free-variable types:\n\t"
           ++ pretty x ++ "\nwith\n\t" ++ pretty y


isType :: (Id, CKind) -> Bool
isType (_, CConstr "Type") = True
isType _                   = False

freshPolymorphicInstance :: TypeScheme -> MaybeT Checker Type
freshPolymorphicInstance (Forall s kinds ty) = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- mapM instantiateVariable kinds
    return $ renameType renameMap ty

  where
    -- Freshen variables, create existential instantiation
    instantiateVariable (var, k) = do
      -- Freshen the variable depending on its kind
      var' <- case k of
               KType -> do
                 freshName <- freshVar (sourceName var)
                 let var'  = changeInternalRepr var freshName
                 -- Label fresh variable as an existential
                 modify (\st -> st { tyVarContext = (var', (k, InstanceQ)) : tyVarContext st })
                 return var'
               KConstr c -> freshCoeffectVar var (CConstr c)
               KCoeffect ->
                 error "Coeffect kind variables not yet supported"
               KFun _ _ -> unhandled
               KPoly _ -> unhandled
      -- Return pair of old variable name and instantiated name (for
      -- name map)
      return (var, var')

relevantSubCtxt :: [Id] -> [(Id, t)] -> [(Id, t)]
relevantSubCtxt vars = filter relevant
 where relevant (var, _) = var `elem` vars


isNonLinearAssumption :: (Id, Assumption) -> Bool
isNonLinearAssumption (_, Discharged _ _) = True
isNonLinearAssumption _                   = False

-- Replace all top-level discharged coeffects with a variable
-- and derelict anything else
-- but add a var
discToFreshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption -> Coeffect
  -> MaybeT Checker (Ctxt Assumption)
discToFreshVarsIn s vars ctxt coeffect = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      kind <- mguCoeffectTypes s c coeffect
      -- Create a fresh variable
      cvar  <- freshCoeffectVar var kind
      -- Return the freshened var-type mapping
      return (var, Discharged t (CVar cvar))

    toFreshVar (var, Linear t) = do
      kind <- inferCoeffectType s coeffect
      return (var, Discharged t (COne kind))


-- `freshVarsIn names ctxt` creates a new context with
-- all the variables names in `ctxt` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Discharged (2, Int),
--                           ("y", Linear Int),
--                           ("z", Discharged (3, Int)]
--  -> [("x", Discharged (c5 :: Nat, Int),
--      ("y", Linear Int)]
--
freshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
freshVarsIn s vars ctxt = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      ctype <- inferCoeffectType s c
      -- Create a fresh variable
      freshName <- freshVar (sourceName var)
      let cvar = changeInternalRepr var freshName
      -- Update the coeffect kind context
      modify (\s -> s { tyVarContext = (cvar, (liftCoeffectType ctype, InstanceQ)) : tyVarContext s })
      -- Return the freshened var-type mapping
      return (var, Discharged t (CVar cvar))

    toFreshVar (var, Linear t) = return (var, Linear t)

-- Combine two contexts
ctxPlus :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
ctxPlus _ [] ctxt2 = return ctxt2
ctxPlus s ((i, v) : ctxt1) ctxt2 = do
  ctxt' <- extCtxt s ctxt2 i v
  ctxPlus s ctxt1 ctxt'

-- Erase a variable from the context
eraseVar :: Ctxt Assumption -> Id -> Ctxt Assumption
eraseVar [] _ = []
eraseVar ((var, t):ctxt) var' | var == var' = ctxt
                             | otherwise = (var, t) : eraseVar ctxt var'

-- ExtCtxt the context
extCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Id -> Assumption
  -> MaybeT Checker (Ctxt Assumption)
extCtxt s ctxt var (Linear t) = do

  case lookup var ctxt of
    Just (Linear t') ->
       if t == t'
        then halt $ LinearityError (Just s)
                  $ "Linear variable `" ++ pretty var ++ "` is used more than once.\n"
        else halt $ GenericError (Just s)
                   $ "Type clash for variable `" ++ pretty var ++ "`"
    Just (Discharged t' c) ->
       if t == t'
         then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
         else halt $ GenericError (Just s)
                   $ "Type clash for variable " ++ pretty var ++ "`"
    Nothing -> return $ (var, Linear t) : ctxt

extCtxt s ctxt var (Discharged t c) = do

  case lookup var ctxt of
    Just (Discharged t' c') ->
        if t == t'
        then return $ replace ctxt var (Discharged t' (c `CPlus` c'))
        else do
          halt $ GenericError (Just s)
               $ "Type clash for variable `" ++ pretty var ++ "`"
    Just (Linear t') ->
        if t == t'
        then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
        else do
          halt $ GenericError (Just s)
               $ "Type clash for variable " ++ pretty var ++ "`"
    Nothing -> return $ (var, Discharged t c) : ctxt

-- Helper, foldM on a list with at least one element
fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M _ []     = error "Must have at least one case"
fold1M f (x:xs) = foldM f x xs

lookupMany :: Eq a => a -> [(a, b)] -> [b]
lookupMany _ []                     = []
lookupMany a' ((a, b):xs) | a == a' = b : lookupMany a' xs
lookupMany a' (_:xs)                = lookupMany a' xs
