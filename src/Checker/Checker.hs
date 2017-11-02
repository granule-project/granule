{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Checker.Checker where

import Syntax.Expr
import Syntax.Pretty
import Checker.Types
import Checker.Coeffects
import Checker.Constraints
import Checker.Environment
import Context
import Prelude hiding (pred)

import Data.List
import Data.Maybe
import Control.Monad.State.Strict
import Control.Monad.Reader.Class
import Control.Monad.Trans.Maybe
import Data.SBV hiding (kindOf)
import Debug.Trace

-- Checking (top-level)
check :: [Def]        -- List of definitions
      -> Bool         -- Debugging flag
      -> [(Id, Id)]   -- Name map
      -> IO (Either String Bool)
check defs dbg nameMap = do
    -- Get the types of all definitions (assume that they are correct for
    -- the purposes of (mutually)recursive calls).

    -- Build a computation which checks all the defs (in order)...
    let defEnv = map (\(Def _ var _ _ tys) -> (var, tys)) defs
    let checkedDefs = mapM (checkDef dbg defEnv) defs
    -- ... and evaluate the computation with initial state
    results <- evalChecker initState nameMap checkedDefs

    -- If all definitions type checked, then the whole file type checkers
    if all isJust results
      then return . Right $ True
      else return . Left  $ ""

checkDef :: Bool           -- turn on debgging
        -> Env TypeScheme  -- environment of top-level definitions
        -> Def             -- definition
        -> Checker (Maybe (Env TyOrDisc))
checkDef dbg defEnv (Def s name expr pats (Forall _ ckinds ty)) = do
    env <- runMaybeT $ do
      checkerState <- get
      put checkerState { ckenv = map (\(n, c) -> (n, (c, ForallQ))) ckinds }
      newConjunct
      -- check expression against type
      env <- case (ty, pats) of
        (FunTy _ _, pats@(_:_)) -> do

          (localGam, ty') <- ctxtFromTypedPatterns dbg s ty pats
          -- Check the body in the extended context
          localGam' <- checkExpr dbg defEnv localGam Negative ty' expr
          -- Check linear use
          case remainingUndischarged localGam localGam' of
                [] -> return localGam'
                xs -> do
                   nameMap  <- ask
                   illLinearity s
                    . intercalate "\n"
                    . map (unusedVariable . unrename nameMap . fst) $ xs
        (tau, []) -> checkExpr dbg defEnv [] Positive tau expr
        _         -> illTyped s "Expecting a function type"
      state <- get
      let pred = predicate state
      let predStack = predicateStack state
      solved <- solveConstraints (Conj $ pred : predStack) s name
      if solved
        then return env
        else illTyped s "Constraints violated"
    -- Erase the solver predicate between definitions
    checkerState <- get
    put (checkerState { predicate = Conj [], predicateStack = [], ckenv = [], cVarEnv = [] })
    return env

-- ctxtFromTypedPatterns ::
ctxtFromTypedPatterns dbg s ty [] =
  return ([], ty)
ctxtFromTypedPatterns dbg s (FunTy t1 t2) (pat:pats) = do
  ctx <- ctxtFromTypedPattern dbg s t1 pat
  case ctx of
    Just localGam -> do
      (localGam', ty) <- ctxtFromTypedPatterns dbg s t2 pats
      return (localGam ++ localGam', ty)
    Nothing -> illTypedPattern s t1 pat

data Polarity = Positive | Negative deriving Show


flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

-- Type check an expression

--  `checkExpr dbg defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in environment `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: Bool             -- turn on debgging
          -> Env TypeScheme   -- environment of top-level definitions
          -> Env TyOrDisc     -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Type             -- type
          -> Expr             -- expression
          -> MaybeT Checker (Env TyOrDisc)

-- Checking of constants

checkExpr _ _ _ _ (ConT "Int") (Val _ (NumInt _)) = return []
  -- Automatically upcast integers to floats
checkExpr _ _ _ _ (ConT "Float") (Val _ (NumInt _)) = return []
checkExpr _ _ _ _ (ConT "Float") (Val _ (NumFloat _)) = return []

checkExpr dbg defs gam pol (FunTy sig tau) (Val s (Abs x t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here
  case t of
    Nothing -> return ()
    Just t' -> do
      eqT <- equalTypes dbg s sig t'
      if eqT
        then return ()
        else illTyped s $ pretty t' ++ " not equal to " ++ pretty t'

  -- Extend the context with the variable 'x' and its type
  gamE <- extCtxt s gam x (Left sig)
  -- Check the body in the extended context
  gam' <- checkExpr dbg defs gamE pol tau e
  -- Linearity check, variables must be used exactly once
  case lookup x gam' of
    Nothing -> do
      nameMap <- ask
      illLinearity s $ unusedVariable (unrename nameMap x)
    Just _  -> return (eraseVar gam' x)

checkExpr _ _ _ _ tau (Val s (Abs {})) =
    illTyped s $ "Expected a function type, but got " ++ pretty tau

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr dbg defs gam pol (Box demand tau) (Val s (Promote e)) = do
  gamF    <- discToFreshVarsIn s (fvs e) gam demand
  gam'    <- checkExpr dbg defs gamF pol tau e

  let gam'' = multAll (fvs e) demand gam'
  case pol of
      Positive -> leqCtxt s gam'' gam
      Negative -> leqCtxt s gam gam''
  return gam''

-- Application
checkExpr dbg defs gam pol tau (App s e1 e2) = do
    (sig, gam1) <- synthExpr dbg defs gam pol e2
    gam2 <- checkExpr dbg defs gam pol (FunTy sig tau) e1
    ctxPlus s gam1 gam2

checkExpr dbg defs gam pol tau (Case s guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam) <- synthExpr dbg defs gam pol guardExpr
  -- then synthesise the types of the branches
  branchCtxts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding environment for the branch pattern
      newConjunct
      localGamMaybe <- ctxtFromTypedPattern dbg s ty pati
      newConjunct
      ---
      case localGamMaybe of
        Just localGam -> do
          localGam' <- checkExpr dbg defs (gam ++ localGam) pol tau ei
          concludeImplication
          -- Check linear use in anything left
          nameMap  <- ask
          case remainingUndischarged localGam localGam' of
            [] -> return localGam'
            xs -> illLinearity s $ intercalate "\n" $ map (unusedVariable . unrename nameMap . fst) xs

        Nothing  -> illTyped (getSpan guardExpr)
                          $ "Type of guard does not match type of the pattern "
                         ++ pretty pati

  -- Find the upper-bound contexts
  nameMap     <- ask
  branchesGam <- foldM (joinCtxts s nameMap) empty branchCtxts
  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxPlus s branchesGam guardGam
  return gamNew


-- all other rules, go to synthesis
checkExpr dbg defs gam pol tau e = do
  (tau', gam') <- synthExpr dbg defs gam (flipPol pol) e
  tyEq <-
    case pol of
      Positive -> do
        dbgMsg dbg $ "+ Compare for equality " ++ pretty tau' ++ " = " ++ pretty tau
        leqCtxt (getSpan e) gam gam'
        equalTypes dbg (getSpan e) tau' tau

      -- i.e., this check is from a synth
      Negative -> do
        dbgMsg dbg $ "- Compare for equality " ++ pretty tau ++ " = " ++ pretty tau'
        leqCtxt (getSpan e) gam gam'
        equalTypes dbg (getSpan e) tau' tau

  if tyEq
    then return gam'
    else illTyped (getSpan e)
            $ "Expected '" ++ pretty tau ++ "' but got '" ++ pretty tau' ++ "'"

-- Essentially equality on types but join on any coeffects
joinTypes :: Bool -> Span -> Type -> Type -> MaybeT Checker Type
joinTypes dbg s (FunTy t1 t2) (FunTy t1' t2') = do
  t1j <- joinTypes dbg s t1' t1 -- contravariance
  t2j <- joinTypes dbg s t2 t2'
  return (FunTy t1j t2j)

joinTypes _ _ (ConT t) (ConT t') | t == t' = return (ConT t)

joinTypes dbg s (Diamond ef t) (Diamond ef' t') = do
  tj <- joinTypes dbg s t t'
  if ef == ef'
    then return (Diamond ef tj)
    else do
      illGraded s $ "Effect mismatch: " ++ pretty ef ++ " not equal to " ++ pretty ef'
      halt

joinTypes dbg s (Box c t) (Box c' t') = do
  kind <- mguCoeffectKinds s c c'
  -- Create a fresh coeffect variable
  topVar <- freshCoeffectVar "" kind
  -- Unify the two coeffects into one
  addConstraint (Leq s c  (CVar topVar) kind)
  addConstraint (Leq s c' (CVar topVar) kind)
  tu <- joinTypes dbg s t t'
  return $ Box (CVar topVar) tu


joinTypes dbg s (TyInt n) (TyInt m) | n == m = do
  return $ TyInt n

joinTypes dbg s (TyInt n) (TyVar m) = do
  -- Create a fresh coeffect variable
  let kind = CConstr "Nat="
  var <- freshCoeffectVar m kind
  -- Unify the two coeffects into one
  addConstraint (Eq s (CNat Discrete n) (CVar var) kind)
  return $ TyInt n

joinTypes dbg s (TyVar n) (TyInt m) = do
  joinTypes dbg s (TyInt m) (TyVar n)

joinTypes dbg s (TyVar n) (TyVar m) = do
  -- Create fresh variables for the two tyint variables
  let kind = CConstr "Nat="
  nvar <- freshCoeffectVar n kind
  mvar <- freshCoeffectVar m kind
  -- Unify the two variables into one
  addConstraint (Leq s (CVar nvar) (CVar mvar) kind)
  return $ TyVar n

joinTypes dbg s (TyApp t1 t2) (TyApp t1' t2') = do
  t1'' <- joinTypes dbg s t1 t1'
  t2'' <- joinTypes dbg s t2 t2'
  return (TyApp t1'' t2'')

joinTypes _ s t1 t2 =
  illTyped s
    $ "Type '" ++ pretty t1 ++ "' and '"
               ++ pretty t2 ++ "' have no upper bound"


-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: Bool           -- ^ Whether in debug mode
          -> Env TypeScheme -- ^ Environment of top-level definitions
          -> Env TyOrDisc   -- ^ Local typing context
          -> Polarity       -- ^ Polarity of subgrading
          -> Expr           -- ^ Expression
          -> MaybeT Checker (Type, Env TyOrDisc)

-- Constants (built-in effect primitives)
synthExpr _ _ _ _ (Val _ (Var "read")) = return (Diamond ["R"] (ConT "Int"), [])

synthExpr _ _ _ _ (Val _ (Var "write")) =
  return (FunTy (ConT "Int") (Diamond ["W"] (ConT "Int")), [])

-- Constants (booleans)
synthExpr _ _ _ _ (Val _ (Constr s [])) | s == "False" || s == "True" =
  return (ConT "Bool", [])

-- Constants (numbers)
synthExpr _ _ _ _ (Val _ (NumInt _))  = return (ConT "Int", [])
synthExpr _ _ _ _ (Val _ (NumFloat _)) = return (ConT "Float", [])

-- List constructors
synthExpr _ _ _ _ (Val _ (Constr "Nil" [])) =
  return (TyApp (TyApp (ConT "List") (TyInt 0)) (ConT "Int"), [])

synthExpr _ _ _ _ (Val s (Constr "Cons" [])) = do
    -- Cons : a -> List n a -> List (n + 1) a
    let kind = CConstr "Nat="
    sizeVarArg <- freshCoeffectVar "n" kind
    sizeVarRes <- freshCoeffectVar "m" kind
    -- Add a constraint
    addConstraint $ Eq s (CVar sizeVarRes)
                         (CPlus (CNat Discrete 1) (CVar sizeVarArg)) kind
    return (FunTy (ConT "Int")
             (FunTy (list (TyVar sizeVarArg)) (list (TyVar sizeVarRes))), [])
  where
    list n = TyApp (TyApp (ConT "List") n) (ConT "Int")


-- Effectful lifting
synthExpr dbg defs gam pol (Val _ (Pure e)) = do
  (ty, gam') <- synthExpr dbg defs gam pol e
  return (Diamond [] ty, gam')

-- Case
synthExpr dbg defs gam pol (Case s guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam) <- synthExpr dbg defs gam pol guardExpr
  -- then synthesise the types of the branches
  branchTysAndCtxts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding environment for the branch pattern
      newConjunct
      localGamMaybe <- ctxtFromTypedPattern dbg s ty pati
      newConjunct
      ---
      case localGamMaybe of
        Just localGam -> do
          (tyCase, localGam') <- synthExpr dbg defs (gam ++ localGam) pol ei
          concludeImplication
          -- Check linear use in anything left
          nameMap  <- ask
          case remainingUndischarged localGam localGam' of
            [] -> return (tyCase, localGam')
            xs -> illLinearity s $ intercalate "\n" $ map (unusedVariable . unrename nameMap . fst) xs

        Nothing  -> illTyped (getSpan guardExpr)
                          $ "Type of guard does not match type of the pattern "
                         ++ pretty pati

  let (branchTys, branchCtxts) = unzip branchTysAndCtxts
  let branchTysAndSpans = zip branchTys (map (getSpan . snd) cases)
  -- Finds the upper-bound return type between all branches
  eqTypes <- foldM (\ty2 (ty1, sp) -> joinTypes dbg sp ty1 ty2)
                   (head branchTys)
                   (tail branchTysAndSpans)

  -- Find the upper-bound type on the return contexts
  nameMap     <- ask
  branchesGam <- foldM (joinCtxts s nameMap) empty branchCtxts

  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxPlus s branchesGam guardGam
  dbgMsg dbg $ " eee " ++ pretty gamNew
  return (eqTypes, gamNew)

-- Diamond cut
synthExpr dbg defs gam pol (LetDiamond s var ty e1 e2) = do
  gam'        <- extCtxt s gam var (Left ty)
  (tau, gam1) <- synthExpr dbg defs gam' pol e2
  case tau of
    Diamond ef2 tau' -> do
       (sig, gam2) <- synthExpr dbg defs gam pol e1
       case sig of
         Diamond ef1 ty' | ty == ty' -> do
             gamNew <- ctxPlus s gam1 gam2
             return (Diamond (ef1 ++ ef2) tau', gamNew)
         t -> illTyped s $ "Expected '" ++ pretty ty ++ "' but inferred '" ++ pretty t ++ "' in body of let<>"
    t -> illTyped s $ "Expected '" ++ pretty ty ++ "' in subjet of let<>, but inferred '" ++ pretty t ++ "'"

-- Variables
synthExpr _ defs gam pol (Val s (Var x)) = do
   nameMap <- ask
   case lookup x gam of
     Nothing ->
       case lookup x defs of
         Just tyScheme  -> do
           ty' <- freshPolymorphicInstance tyScheme
           return (ty', [])
         Nothing  -> illTyped s $ "I don't know the type for "
                              ++ show (unrename nameMap x)
                              ++ "{ looking for " ++ x
                              ++ " in environment " ++ pretty gam
                              ++ " or definitions " ++ pretty defs ++ "}"

     Just (Left ty)       -> return (ty, [(x, Left ty)])
     Just (Right (c, ty)) -> do
       k <- kindOf c
       return (ty, [(x, Right (COne k, ty))])

-- Application
synthExpr dbg defs gam pol (App s e e') = do
    (f, gam1) <- synthExpr dbg defs gam pol e
    case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr dbg defs gam Negative sig e'
         gamNew <- ctxPlus s gam1 gam2
         return (tau, gamNew)
      t -> illTyped s $ "Left-hand side of application is not a function"
                   ++ " but has type '" ++ pretty t ++ "'"

-- Promotion
synthExpr dbg defs gam pol (Val s (Promote e)) = do
   dbgMsg dbg $ "Synthing a promotion of " ++ pretty e

   -- Create a fresh kind variable for this coeffect
   vark <- freshVar $ "kprom_" ++ [head (pretty e)]

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshCoeffectVar ("prom_" ++ [head (pretty e)]) (CPoly vark)

   gamF <- discToFreshVarsIn s (fvs e) gam (CVar var)

   (t, gam') <- synthExpr dbg defs gamF pol e
   return (Box (CVar var) t, multAll (fvs e) (CVar var) gam')

-- Letbox
synthExpr dbg defs gam pol (LetBox s var t e1 e2) = do

    -- Create a fresh kind variable for this coeffect
    ckvar <- freshVar ("binderk_" ++ var)
    let kind = CPoly ckvar
    -- Update coeffect-kind environment
    cvar <- freshCoeffectVar ("binder_" ++ var) kind

    -- Extend the context with cvar
    gam' <- extCtxt s gam var (Right (CVar cvar, t))

    (tau, gam2) <- synthExpr dbg defs gam' pol e2

    (demand, t'') <-
      case lookup var gam2 of
        Just (Right (demand, t')) -> do
             eqT <- equalTypes dbg s t' t
             if eqT then do
                dbgMsg dbg $ "Demand for " ++ var ++ " = " ++ pretty demand
                return (demand, t)
              else do
                nameMap <- ask
                illTyped s $ "An explicit signature is given "
                         ++ unrename nameMap var
                         ++ " : '" ++ pretty t
                         ++ "' but the actual type was '" ++ pretty t' ++ "'"
        _ -> do
          -- If there is no explicit demand for the variable
          -- then this means it is not used
          -- Therefore c ~ 0
          addConstraint (Eq s (CVar cvar) (CZero kind) kind)
          return (CZero kind, t)

    gam1 <- checkExpr dbg defs gam (flipPol pol) (Box demand t'') e1
    gamNew <- ctxPlus s gam1 gam2
    return (tau, gamNew)

-- BinOp
synthExpr dbg defs gam pol (Binop s _ e e') = do
    (t, gam1)  <- synthExpr dbg defs gam pol e
    (t', gam2) <- synthExpr dbg defs gam pol e'
    checkerState <- get
    case (t, t') of
        -- Well typed
        (ConT n, ConT m) | isNum n && isNum m -> do
             gamNew <- ctxPlus s gam1 gam2
             return (ConT $ joinNum n m, gamNew)

        -- Or ill-typed
        _ -> illTyped s $ "Binary operator expects two 'Int' expressions "
                     ++ "but got '" ++ pretty t ++ "' and '" ++ pretty t' ++ "'"
  where isNum "Int" = True
        isNum "Float" = True
        isNum _      = False
        joinNum "Int" "Int" = "Int"
        joinNum x "Float" = x
        joinNum "Float" x = x
        joinNum _ _ = error "joinNum is intentionally partial. Please \
                            \create an issue on GitHub!"

-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr dbg defs gam pol (Val s (Abs x (Just sig) e)) = do
  gam' <- extCtxt s gam x (Left sig)
  (tau, gam'') <- synthExpr dbg defs gam' pol e
  return (FunTy sig tau, gam'')

synthExpr _ _ _ _ e = illTyped (getSpan e) $ "I can't work out the type here, try adding more type signatures"


solveConstraints :: Pred -> Span -> String -> MaybeT Checker Bool
solveConstraints pred s defName = do
  -- Get the coeffect kind environment and constraints
  checkerState <- get
  let envCk  = ckenv checkerState
  let envCkVar = cVarEnv checkerState
  --
  let (sbvTheorem, unsats) = compileToSBV pred envCk envCkVar
  thmRes <- liftIO . prove $ sbvTheorem
  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) ->
        illTyped nullSpan $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModelAssignment thmRes of
               -- Main 'Falsifiable' result
               Right (False, _ :: [ Integer ] ) -> do
                   -- Show any trivial inequalities
                   mapM_ (\c -> illGraded (getSpan c) (pretty . Neg $ c)) unsats
                   -- Show fatal error, with prover result
                   illTyped s $ "Definition '" ++ defName ++ "' is shown to be " ++ show thmRes

               Right (True, _) ->
                   illTyped s $ "Definition '" ++ defName ++ "' returned probable model."

               Left str        ->
                   illTyped s $ "Definition '" ++ defName ++ " had a solver fail: " ++ str

           else return True

leqCtxt :: Span -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker ()
leqCtxt s env1 env2 = do
    let env  = env1 `keyIntersect` env2
        env' = env2 `keyIntersect` env1
    zipWithM_ (leqAssumption s) env env'

joinCtxts :: Span -> [(Id, Id)] -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
joinCtxts s nameMap env1 env2 = do
    -- All the type assumptions from env1 whose variables appear in env2
    -- and weaken all others
    env  <- env1 `keyIntersectWithWeaken` env2
    -- All the type assumptions from env2 whose variables appear in env1
    -- and weaken all others
    env' <- env2 `keyIntersectWithWeaken` env1

    -- Make an environment with fresh coeffect variables for all
    -- the variables which are in both env1 and env2...
    varEnv <- freshVarsIn (map fst env) env
    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in env and env'
    zipWithM_ (leqAssumption s) env varEnv
    zipWithM_ (leqAssumption s) env' varEnv
    -- Return the common upper-bound environment with the disjoint parts
    -- of env1 and env2
    return $ varEnv ++ (env1 `keyDelete` varEnv) ++ (env2 `keyDelete` varEnv)

keyIntersectWithWeaken ::
  Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
keyIntersectWithWeaken a b = do
    let intersected = keyIntersect a b
    let remaining   = a `keyDelete` intersected
    weakenedRemaining <- mapM weaken remaining
    let newCtxt = intersected ++ filter isNonLinearAssumption weakenedRemaining
    return $ sortBy (\x y -> fst x `compare` fst y) newCtxt
  where
   isNonLinearAssumption :: (Id, TyOrDisc) -> Bool
   isNonLinearAssumption (_, Right _) = True
   isNonLinearAssumption _            = False

   weaken :: (Id, TyOrDisc) -> MaybeT Checker (Id, TyOrDisc)
   weaken (var, Left t) = do
     return (var, Left t)
   weaken (var, Right (c, t)) = do
     kind <- kindOf c
     return (var, Right (CZero kind, t))

remainingUndischarged :: Env TyOrDisc -> Env TyOrDisc -> Env TyOrDisc
remainingUndischarged env subEnv =
  deleteFirstsBy linearCancel (lefts' env) (lefts' subEnv)
    where
      lefts' = filter isLeftPair
      isLeftPair (_, Left _) = True
      isLeftPair (_, _)      = False
      linearCancel (v, Left t) (v', Left t') = v == v'
      linearCancel (v, Left t) (v', Right (CZero _, t')) = v == v'
      linearCancel (v, Right (CZero _, t')) (v', Left t) = v == v'
      linearCancel (v, Right a) (v', Right  _)           = v == v'
      linearCancel _ _ = False

leqAssumption ::
    Span -> (Id, TyOrDisc) -> (Id, TyOrDisc) -> MaybeT Checker ()

-- Linear assumptions ignored
leqAssumption _ (_, Left _)        (_, Left _) = return ()

-- Discharged coeffect assumptions
leqAssumption s (_, Right (c1, _)) (_, Right (c2, _)) = do
  kind <- mguCoeffectKinds s c1 c2
  addConstraint (Leq s c1 c2 kind)

leqAssumption s (x, t) (x', t') = do
  nameMap <- ask
  illTyped s $ "Can't unify free-variable types:\n\t"
           ++ pretty (unrename nameMap x, t)
           ++ "\nwith\n\t" ++ pretty (unrename nameMap x', t')


freshPolymorphicInstance :: TypeScheme -> MaybeT Checker Type
freshPolymorphicInstance (Forall s ckinds ty) = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- mapM (\(c, k) -> fmap (\c' -> (c, c')) (freshCoeffectVar c k)) ckinds
    rename renameMap ty

  where
    rename renameMap (FunTy t1 t2) = do
      t1' <- rename renameMap t1
      t2' <- rename renameMap t2
      return $ FunTy t1' t2'
    rename renameMap (Box c t) = do
      c' <- renameC s renameMap c
      t' <- rename renameMap t
      return $ Box c' t'
    rename renameMap (TyApp t1 t2) = do
      t1' <- rename renameMap t1
      t2' <- rename renameMap t2
      return $ TyApp t1' t2'
    rename renameMap (TyVar v) = do
      case lookup v renameMap of
        Just v' -> return $ TyVar v'
        Nothing -> illTyped s $ "Type variable " ++ v ++ " is unbound"
    rename _ t = return t

relevantSubEnv :: [Id] -> [(Id, t)] -> [(Id, t)]
relevantSubEnv vars env = filter relevant env
 where relevant (var, _) = var `elem` vars

-- Replace all top-level discharged coeffects with a variable
-- and derelict anything else
-- but add a var
discToFreshVarsIn :: Span -> [Id] -> Env TyOrDisc -> Coeffect -> MaybeT Checker (Env TyOrDisc)
discToFreshVarsIn s vars env coeffect = mapM toFreshVar (relevantSubEnv vars env)
  where
    toFreshVar (var, Right (c, t)) = do
      kind <- mguCoeffectKinds s c coeffect
      -- Create a fresh variable
      cvar  <- freshCoeffectVar var kind
      -- Return the freshened var-type mapping
      return (var, Right (CVar cvar, t))

    toFreshVar (var, Left t) = do
      kind <- kindOf coeffect
      return (var, Right (COne kind, t))


-- `freshVarsIn names env` creates a new environment with
-- all the variables names in `env` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Right (2, Int),
--                           ("y", Left Int),
--                           ("z", Right (3, Int)]
--  -> [("x", Right (c5 :: Nat, Int),
--      ("y", Left Int)]
--
freshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
freshVarsIn vars env = mapM toFreshVar (relevantSubEnv vars env)
  where
    toFreshVar (var, Right (c, t)) = do
      ckind <- kindOf c
      -- Create a fresh variable
      cvar  <- freshVar var
      -- Update the coeffect kind environment
      modify (\s -> s { ckenv = (cvar, (ckind, ExistsQ)) : ckenv s })
      -- Return the freshened var-type mapping
      return (var, Right (CVar cvar, t))

    toFreshVar (var, Left t) = return (var, Left t)

-- Combine two contexts
ctxPlus :: Span -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
ctxPlus _ [] env2 = return env2
ctxPlus s ((i, v) : env1) env2 = do
  env' <- extCtxt s env2 i v
  ctxPlus s env1 env'

-- Erase a variable from the environment
eraseVar :: Env TyOrDisc -> Id -> Env TyOrDisc
eraseVar [] _ = []
eraseVar ((var, t):env) var' | var == var' = env
                             | otherwise = (var, t) : eraseVar env var'

-- ExtCtxt the environment
extCtxt :: Span -> Env TyOrDisc -> Id -> TyOrDisc -> MaybeT Checker (Env TyOrDisc)
extCtxt s env var (Left t) = do
  nameMap <- ask
  let var' = unrename nameMap var
  case lookup var env of
    Just (Left t') ->
       if t == t'
        then illLinearity s $ "Linear variable `" ++ var' ++ "` is used more than once.\n"
        else illTyped s $ "Type clash for variable `" ++ var' ++ "`"
    Just (Right (c, t')) ->
       if t == t'
         then do
           k <- kindOf c
           return $ replace env var (Right (c `CPlus` COne k, t))
         else illTyped s $ "Type clash for variable " ++ var' ++ "`"
    Nothing -> return $ (var, Left t) : env

extCtxt s env var (Right (c, t)) = do
  nameMap <- ask
  case lookup var env of
    Just (Right (c', t')) ->
        if t == t'
        then return $ replace env var (Right (c `CPlus` c', t'))
        else do
          let var' = unrename nameMap var
          illTyped s $ "Type clash for variable `" ++ var' ++ "`"
    Just (Left t') ->
        if t == t'
        then do
           k <- kindOf c
           return $ replace env var (Right (c `CPlus` COne k, t))
        else do
          let var' = unrename nameMap var
          illTyped s $ "Type clash for variable " ++ var' ++ "`"
    Nothing -> return $ (var, Right (c, t)) : env