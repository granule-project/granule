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

-- Checking (top-level)
check :: [Def]        -- List of definitions
      -> Bool         -- Debugging flag
      -> [(Id, Id)]   -- Name map
      -> IO (Either String Bool)
check defs dbg nameMap = do
    -- Get the types of all definitions (assume that they are correct for
    -- the purposes of (mutually)recursive calls).
    let defEnv = map (\(Def var _ _ tys) -> (var, tys)) defs

    -- Build a computation which checks all the defs (in order)...
    let checkedDefs = mapM (checkDef defEnv) defs
    -- ... and evaluate the computation with initial state
    results <- evalChecker initState nameMap checkedDefs

    -- If all definitions type checked, then the whole file type checkers
    if all (\(_, _, _, checked) -> isJust checked) $ results
      then return . Right $ True
      -- Otherwise, show the checking reports
      else return . Left  $ intercalate "\n" (filter (/= "") $ map mkReport results)
  where
    checkDef defEnv (Def var expr _ tys) = do
      env' <- runMaybeT $ do
               env' <- checkExprTS dbg defEnv [] tys expr
               solved <- solveConstraints
               if solved
                 then return ()
                 else illTyped "Constraints violated"
               return env'
      -- Erase the solver predicate between definitions
      checkerState <- get
      put (checkerState { predicate = [], ckenv = [] })
      return (var, tys, Nothing, env')

-- Make type error report
mkReport :: (Id, TypeScheme, Maybe TypeScheme, Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, synthTy, Nothing) =
    "'" ++ var ++ "' does not type check, signature was: " ++ pretty ty
        ++ (case synthTy of { Nothing -> ""; Just ty' -> "\n but infered: " ++ pretty ty' })

mkReport _ = ""

-- Type check an expression

--  `checkExpr dbg defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in environment `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExprTS :: Bool          -- turn on debgging
          -> Env TypeScheme  -- environment of top-level definitions
          -> Env TyOrDisc    -- local typing context
          -> TypeScheme      -- typeScheme
          -> Expr            -- expression
          -> MaybeT Checker (Env TyOrDisc)

checkExprTS dbg defs gam (Forall ckinds ty) e = do
  -- Coeffect kinds only need a local resolution; set kind environment to scheme
  checkerState <- get
  put checkerState { ckenv = ckinds }
  -- check expression against type
  checkExpr dbg defs gam Positive ty e

data Polarity = Positive | Negative deriving Show


flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

checkExpr :: Bool             -- turn on debgging
          -> Env TypeScheme   -- environment of top-level definitions
          -> Env TyOrDisc     -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Type             -- type
          -> Expr             -- expression
          -> MaybeT Checker (Env TyOrDisc)

-- Checking of constants

checkExpr _ _ _ _ (ConT "Int") (Val (NumInt _)) = return []
  -- Automatically upcast integers to reals
checkExpr _ _ _ _ (ConT "Real") (Val (NumInt _)) = return []
checkExpr _ _ _ _ (ConT "Real") (Val (NumReal _)) = return []

checkExpr dbg defs gam pol (FunTy sig tau) (Val (Abs x t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here
  case t of
    Nothing -> return ()
    Just t' -> do
      eqT <- equalTypes dbg sig t'
      if eqT
        then return ()
        else illTyped $ "Type mismatch: " ++ pretty sig ++ " != " ++ pretty t'

  -- Extend the context with the variable 'x' and its type
  gamE <- extCtxt gam x (Left sig)
  -- Check the body in the extended context
  gam' <- checkExpr dbg defs gamE pol tau e
  -- Linearity check, variables must be used exactly once
  case lookup x gam' of
    Nothing -> do
      nameMap <- ask
      illTyped $ unusedVariable (unrename nameMap x)
    Just _  -> return (eraseVar gam' x)

checkExpr _ _ _ _ tau (Val Abs {}) =
    illTyped $ "Expected a function type, but got " ++ pretty tau

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr dbg defs gam pol (Box demand tau) (Val (Promote e)) = do
    gamF    <- discToFreshVarsIn (fvs e) gam demand
    gam'    <- checkExpr dbg defs gamF pol tau e
    let gam'' = multAll (fvs e) demand gam'
    gam `leqCtxt` gam''
    return gam''

-- Application
checkExpr dbg defs gam pol tau (App e1 e2) = do
    (sig, gam1) <- synthExpr dbg defs gam e2
    gam2 <- checkExpr dbg defs gam pol (FunTy sig tau) e1
    gam1 `ctxPlus` gam2

-- all other rules, go to synthesis
checkExpr dbg defs gam pol tau e = do
  (tau', gam') <- synthExpr dbg defs gam e
  tyEq <- case pol of
            Positive -> do
              when dbg $ liftIO $ putStrLn $ "+ Compare for equality " ++ show tau' ++ " = " ++ show tau
              equalTypes dbg tau' tau
            -- i.e., this check is from a synth
            Negative -> do
              when dbg $ liftIO $ putStrLn $ "- Compare for equality " ++ show tau ++ " = " ++ show tau'
              equalTypes dbg tau tau'
  gam' `leqCtxt` gam
  if tyEq then return gam'
          else illTyped $ "Checking: (" ++ pretty e ++ "), "
                        ++ show tau ++ " != " ++ show tau'

-- Check whether two types are equal, and at the same time
-- generate coeffect equality constraints
--
-- The first argument is taken to be possibly approximated by the second
-- e.g., the first argument is inferred, the second is a specification
-- being checked against
equalTypes :: Bool -> Type -> Type -> MaybeT Checker Bool
equalTypes dbg (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- equalTypes dbg t1' t1 -- contravariance
  eq2 <- equalTypes dbg t2 t2' -- covariance
  return (eq1 && eq2)

equalTypes _ (ConT con) (ConT con') = return (con == con')

equalTypes dbg (Diamond ef t) (Diamond ef' t') = do
  eq <- equalTypes dbg t t'
  if ef == ef'
    then return eq
    else illTyped $ "Effect mismatch: " ++ pretty ef ++ "!=" ++ pretty ef'

equalTypes dbg (Box c t) (Box c' t') = do
  -- Debugging
  when dbg $ liftIO $ putStrLn $ pretty c ++ " == " ++ pretty c'
  when dbg $ liftIO $ putStrLn $ "[ " ++ show c ++ " , " ++ show c' ++ "]"
  -- Unify the coeffect kinds of the two coeffects
  kind <- mguCoeffectKinds c c'
  addConstraint (Leq c c' kind)
  equalTypes dbg t t'

equalTypes _ t1 t2 =
  illTyped $ "Type " ++ pretty t1 ++ " != " ++ pretty t2

-- Essentially equality on types but join on any coeffects
joinTypes :: Bool -> Type -> Type -> MaybeT Checker Type
joinTypes dbg (FunTy t1 t2) (FunTy t1' t2') = do
  t1j <- joinTypes dbg t1' t1 -- contravariance
  t2j <- joinTypes dbg t2 t2'
  return (FunTy t1j t2j)

joinTypes _ (ConT t) (ConT t') | t == t' = return (ConT t)

joinTypes dbg (Diamond ef t) (Diamond ef' t') = do
  tj <- joinTypes dbg t t'
  if ef == ef'
    then return (Diamond ef tj)
    else illTyped $ "Effect mismatch: " ++ pretty ef ++ "!=" ++ pretty ef'

joinTypes dbg (Box c t) (Box c' t') = do
  kind <- mguCoeffectKinds c c'
  -- Create a fresh coeffect variable
  topVar <- freshVar ""
  checkerState <- get
  put $ checkerState { ckenv = (topVar, kind) : ckenv checkerState }
  -- Unify the two coeffects into one
  addConstraint (Leq c  (CVar topVar) kind)
  addConstraint (Leq c' (CVar topVar) kind)
  tu <- joinTypes dbg t t'
  return $ Box (CVar topVar) tu

joinTypes _ t1 t2 =
  illTyped $ "Type " ++ pretty t1 ++ " and "
                     ++ pretty t2 ++ " have no upper bound"


-- Synthesise types on expressions
synthExpr :: Bool
          -> Env TypeScheme
          -> Env TyOrDisc
          -> Expr
          -> MaybeT Checker (Type, Env TyOrDisc)

-- Constants (built-in effect primitives)
synthExpr _ _ _ (Val (Var "read")) = return (Diamond ["R"] (ConT "Int"), [])

synthExpr _ _ _ (Val (Var "write")) =
  return (FunTy (ConT "Int") (Diamond ["W"] (ConT "Int")), [])

-- Constants (booleans)
synthExpr _ _ _ (Val (Constr s)) | s == "False" || s == "True" =
  return (ConT "Bool", [])

-- Constants (numbers)
synthExpr _ _ _ (Val (NumInt _))  = return (ConT "Int", [])
synthExpr _ _ _ (Val (NumReal _)) = return (ConT "Real", [])

-- Effectful lifting
synthExpr dbg defs gam (Val (Pure e)) = do
  (ty, gam') <- synthExpr dbg defs gam e
  return (Diamond [] ty, gam')

-- Case
synthExpr dbg defs gam (Case guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam) <- synthExpr dbg defs gam guardExpr
  -- then synthesise the types of the branches
  branchTysAndCtxts <-
    forM cases $ \(pati, ei) ->
      -- Build the binding environment for the branch pattern
      case ctxtFromTypedPattern ty pati of
        Just localGam -> do
          (_, localGam') <- synthExpr dbg defs (gam ++ localGam) ei
          -- Check linear use in anything left
          nameMap  <- ask
          case remainingUndischarged localGam localGam' of
            [] -> return (ty, localGam')
            xs -> illTyped $ intercalate "\n" $ map (unusedVariable . unrename nameMap . fst) xs

        Nothing       -> illTyped $ "Type of the guard expression " ++ pretty ei
                                ++ " does not match the type of the pattern "
                                ++ pretty pati

  let (branchTys, branchCtxts) = unzip branchTysAndCtxts

  -- Finds the upper-bound return type between all branches
  eqTypes <- foldM (joinTypes dbg) (head branchTys) (tail branchTys)

  -- Find the upper-bound type on the return contexts
  nameMap     <- ask
  branchesGam <- foldM (joinCtxts nameMap) empty branchCtxts

  -- Contract the outgoing context of the gurad and the branches (joined)
  gamNew <- branchesGam `ctxPlus` guardGam
  return (eqTypes, gamNew)

-- Diamond cut
synthExpr dbg defs gam (LetDiamond var ty e1 e2) = do
  gam'        <- extCtxt gam var (Left ty)
  (tau, gam1) <- synthExpr dbg defs gam' e2
  case tau of
    Diamond ef2 tau' -> do
       (sig, gam2) <- synthExpr dbg defs gam e1
       case sig of
         Diamond ef1 ty' | ty == ty' -> do
             gamNew <- gam1 `ctxPlus` gam2
             return (Diamond (ef1 ++ ef2) tau', gamNew)
         t -> illTyped $ "Expected a type " ++ pretty ty ++  "but in result of let<>, but inferred " ++ pretty t
    t -> illTyped $ "Expected a diamond type in subjet of let<>, but inferred " ++ pretty t

-- Variables
synthExpr _ defs gam (Val (Var x)) = do
   nameMap <- ask
   case lookup x gam of
     Nothing ->
       case lookup x defs of
         Just tyScheme  -> do
           ty' <- freshPolymorphicInstance tyScheme
           return (ty', [])
         Nothing  -> illTyped $ "I don't know the type for "
                              ++ show (unrename nameMap x)
                              ++ " in environment " ++ pretty gam
                              ++ " or definitions " ++ pretty defs

     Just (Left ty)       -> return (ty, [(x, Left ty)])
     Just (Right (c, ty)) -> do
       k <- kindOf c
       return (ty, [(x, Right (COne k, ty))])

-- Application
synthExpr dbg defs gam (App e e') = do
    (f, gam1) <- synthExpr dbg defs gam e
    case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr dbg defs gam Negative sig e'
         gamNew <- gam1 `ctxPlus` gam2
         return (tau, gamNew)
      _ -> illTyped "Left-hand side of app is not a function type"

-- Promotion
synthExpr dbg defs gam (Val (Promote e)) = do
   when dbg $ liftIO $ putStrLn $ "Synthing a promotion of " ++ pretty e
   -- Create a fresh coeffect variable for the coeffect of the promoting thing
   var <- freshVar $ "prom_" ++ [head (pretty e)]

   -- Create a fresh kind variable for this coeffect
   vark <- freshVar $ "kprom_" ++ [head (pretty e)]
   -- Update coeffect-kind environment
   checkerState <- get
   put $ checkerState { ckenv = (var, CPoly vark) : ckenv checkerState }

   gamF <- discToFreshVarsIn (fvs e) gam (CVar var)

   (t, gam') <- synthExpr dbg defs gamF e
   return (Box (CVar var) t, multAll (fvs e) (CVar var) gam')

-- Letbox
synthExpr dbg defs gam (LetBox var t k e1 e2) = do

    cvar <- freshVar ("binder_" ++ var)
    -- Update coeffect-kind environment
    checkerState <- get
    put $ checkerState { ckenv = (cvar, k) : ckenv checkerState }

    gam' <- extCtxt gam var (Right (CVar cvar, t))

    (tau, gam2) <- synthExpr dbg defs gam' e2
    (demand, t'') <-
      case lookup var gam2 of
        Just (Right (demand, t')) -> do
             eqT <- equalTypes dbg t' t
             if eqT then do
                when dbg $ liftIO . putStrLn $
                     "Demand for " ++ var ++ " = " ++ pretty demand
                return (demand, t)
              else do
                nameMap <- ask
                illTyped $ "An explicit signature is given "
                         ++ unrename nameMap var
                         ++ " : " ++ pretty t
                         ++ " but the actual type was " ++ pretty t'
        _ -> do
          -- If there is no explicit demand for the variable
          -- then this means it is not used
          -- Therefore c ~ 0
          addConstraint (Eq (CVar cvar) (CZero k) k)
          return (CZero k, t)

    gam1 <- checkExpr dbg defs gam Negative (Box demand t'') e1
    gamNew <- gam1 `ctxPlus` gam2
    return (tau, gamNew)


-- BinOp
synthExpr dbg defs gam (Binop _ e e') = do
    (t, gam1)  <- synthExpr dbg defs gam e
    (t', gam2) <- synthExpr dbg defs gam e'
    case (t, t') of
        (ConT n, ConT m) | isNum n && isNum m -> do
            gamNew <- gam1 `ctxPlus` gam2
            return (ConT $ joinNum n m, gamNew)
        _ ->
            illTyped "Binary op does not have two int expressions"
  where isNum "Int" = True
        isNum "Real" = True
        isNum _      = False
        joinNum "Int" "Int" = "Int"
        joinNum x "Real" = x
        joinNum "Real" x = x
        joinNum _ _ = error "joinNum is intentionally partial. Please \
                            \create an issue on GitHub!"

-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr dbg defs gam (Val (Abs x (Just t) e)) = do
  gam' <- extCtxt gam x (Left t)
  synthExpr dbg defs gam' e

synthExpr _ _ _ e = illTyped $ "General synth fail " ++ pretty e


solveConstraints :: MaybeT Checker Bool
solveConstraints = do
  -- Get the coeffect kind environment and constraints
  checkerState <- get
  let env   = ckenv checkerState
  let pred  = predicate checkerState
  --
  let sbvTheorem = compileToSBV pred env
  thmRes <- liftIO . prove $ sbvTheorem
  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) -> illTyped $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModel thmRes of
               Right (False, ce :: [ Integer ] ) -> do
                   satRes <- liftIO . sat $ sbvTheorem
                   let maybeModel = case ce of
                                     [] -> ""
                                     _ -> "Falsifying model: " ++ show ce ++ " - "
                   let satModel = case satRes of
                                    SatResult Unsatisfiable {} -> ""
                                    _ -> "\nSAT result: \n" ++ show satRes
                   illTyped $ show thmRes ++ maybeModel ++ satModel

               Right (True, _) -> illTyped "Returned probable model."
               Left str        -> illTyped $ "Solver fail: " ++ str
           else return True

-- Generate a fresh alphanumeric variable name
freshVar :: String -> MaybeT Checker String
freshVar s = do
  checkerState <- get
  let v = uniqueVarId checkerState
  let prefix = s ++ "_" ++ ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  put $ checkerState { uniqueVarId = v + 1 }
  return cvar

leqCtxt :: Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker ()
leqCtxt env1 env2 = do
    let env  = env1 `keyIntersect` env2
        env' = env2 `keyIntersect` env1
    zipWithM_ leqAssumption env env'

joinCtxts :: [(Id, Id)] -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
joinCtxts nameMap env1 env2 = do
    -- All the type assumptions from env1 whose variables appear in env2
    -- and weaken all others
    env  <- env1 `keyIntersectWithWeaken` env2
    -- All the type assumptions from env2 whose variables appear in env1
    -- and weaken all others
    env' <- env2 `keyIntersectWithWeaken` env1

    -- Check any variables that are not used across branches, e.g.
    -- if `x` is used in one branch but not another
    case remainingUndischarged env1 env ++ remainingUndischarged env2 env' of
      [] -> return ()
      xs -> illTyped $ intercalate "\n" (map (unusedVariable . unrename nameMap . fst) xs)

    -- Make an environment with fresh coeffect variables for all
    -- the variables which are in both env1 and env2...
    varEnv <- freshVarsIn (map fst env) env
    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in env and env'
    zipWithM_ leqAssumption env varEnv
    zipWithM_ leqAssumption env' varEnv
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

isNonLinearAssumption :: (Id, TyOrDisc) -> Bool
isNonLinearAssumption (_, Right _) = True
isNonLinearAssumption _            = False

weaken :: (Id, TyOrDisc) -> MaybeT Checker (Id, TyOrDisc)
weaken (var, Left t) =
  return (var, Left t)
weaken (var, Right (c, t)) = do
  kind <- kindOf c
  return (var, Right (CZero kind, t))

remainingUndischarged :: Env TyOrDisc -> Env TyOrDisc -> Env TyOrDisc
remainingUndischarged env subEnv =
  lefts' env \\ lefts' subEnv
    where
      lefts' = filter isLeftPair
      isLeftPair (_, Left _) = True
      isLeftPair (_, _)      = False

leqAssumption ::
    (Id, TyOrDisc) -> (Id, TyOrDisc) -> MaybeT Checker ()

-- Linear assumptions ignored
leqAssumption (_, Left _)        (_, Left _) = return ()

-- Discharged coeffect assumptions
leqAssumption (_, Right (c1, _)) (_, Right (c2, _)) = do
  kind <- mguCoeffectKinds c1 c2
  addConstraint (Leq c1 c2 kind)

leqAssumption x y =
  illTyped $ "Can't unify free-variable types:\n\t"
           ++ pretty x ++ "\nwith\n\t" ++ pretty y


freshPolymorphicInstance :: TypeScheme -> MaybeT Checker Type
freshPolymorphicInstance (Forall ckinds ty) = do
    renameMap <- mapM freshCoeffectVar ckinds
    rename renameMap ty

  where
    rename renameMap (FunTy t1 t2) = do
      t1' <- rename renameMap t1
      t2' <- rename renameMap t2
      return $ FunTy t1' t2'
    rename renameMap (Box c t) = do
      c' <- renameC renameMap c
      t' <- rename renameMap t
      return $ Box c' t'
    rename _ t = return t

    renameC rmap (CPlus c1 c2) = do
      c1' <- renameC rmap c1
      c2' <- renameC rmap c2
      return $ CPlus c1' c2'

    renameC rmap (CTimes c1 c2) = do
      c1' <- renameC rmap c1
      c2' <- renameC rmap c2
      return $ CTimes c1' c2'

    renameC rmap (CVar v) =
      case lookup v rmap of
        Just v' -> return $ CVar v'
        Nothing -> illTyped $ "Coeffect variable " ++ v ++ " is unbound"

    renameC _ c = return c

    freshCoeffectVar (cvar, kind) = do
      cvar' <- freshVar cvar
      checkerState <- get
      put $ checkerState { ckenv = (cvar', kind) : ckenv checkerState }
      return (cvar, cvar')

relevantSubEnv :: [Id] -> [(Id, t)] -> [(Id, t)]
relevantSubEnv vars env = filter relevant env
 where relevant (var, _) = var `elem` vars

-- Replace all top-level discharged coeffects with a variable
-- and derelict anything else
-- but add a var
discToFreshVarsIn :: [Id] -> Env TyOrDisc -> Coeffect -> MaybeT Checker (Env TyOrDisc)
discToFreshVarsIn vars env coeffect = mapM toFreshVar (relevantSubEnv vars env)
  where
    toFreshVar (var, Right (c, t)) = do
      kind <- mguCoeffectKinds c coeffect
      -- Create a fresh variable
      cvar  <- freshVar var
      -- Update the coeffect kind environment
      modify (\s -> s { ckenv = (cvar, kind) : ckenv s })
      -- Return the freshened var-type mapping
      return (var, Right (CVar cvar, t))

    toFreshVar (var, Left t) = do
      kind <- kindOf coeffect
      return (var, Right (COne kind, t))


-- `freshVarsIn names env` creates a new environment with
-- all the variables names in `env` that appear in the list
-- `names` turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `names` get deleted).
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Right (2, Int),
--                           ("y", Left Int),
--                           ("z", Right (3, Int)]
--  -> [("x", Right (c5 :: Nat, Int),
--      ("y", Right (1, Int))]
--
freshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
freshVarsIn vars env = mapM toFreshVar (relevantSubEnv vars env)
  where
    toFreshVar (var, Right (c, t)) = do
      ckind <- kindOf c
      -- Create a fresh variable
      cvar  <- freshVar var
      -- Update the coeffect kind environment
      modify (\s -> s { ckenv = (cvar, ckind) : ckenv s })
      -- Return the freshened var-type mapping
      return (var, Right (CVar cvar, t))

    toFreshVar (var, Left t) = do
      -- Create a fresh coeffect variable
      cvar  <- freshVar var
      -- Create a fresh kindvariable
      ckind <- freshVar var
      -- Update the coeffect kind environment
      modify (\s -> s { ckenv = (cvar, CPoly ckind) : ckenv s })
      return (var, Right (COne (CPoly ckind), t))


-- Combine two contexts
ctxPlus :: Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
ctxPlus [] env2 = return env2
ctxPlus ((i, v) : env1) env2 = do
  env' <- extCtxt env2 i v
  ctxPlus env1 env'

-- Erase a variable from the environment
eraseVar :: Env TyOrDisc -> Id -> Env TyOrDisc
eraseVar [] _ = []
eraseVar ((var, t):env) var' | var == var' = env
                             | otherwise = (var, t) : eraseVar env var'

-- ExtCtxt the environment
extCtxt :: Env TyOrDisc -> Id -> TyOrDisc -> MaybeT Checker (Env TyOrDisc)
extCtxt env var (Left t) = do
  nameMap <- ask
  let var' = unrename nameMap var
  case lookup var env of
    Just (Left t') ->
       if t == t'
        then illTyped $ "'" ++ var' ++ "' used more than once\n"
        else illTyped $ "Type clash for variable " ++ var'
    Just (Right (c, t')) ->
       if t == t'
         then do
           k <- kindOf c
           return $ replace env var (Right (c `CPlus` COne k, t))
         else illTyped $ "Type clash for variable " ++ var'
    Nothing -> return $ (var, Left t) : env

extCtxt env var (Right (c, t)) = do
  nameMap <- ask
  case lookup var env of
    Just (Right (c', t')) ->
        if t == t'
        then return $ replace env var (Right (c `CPlus` c', t'))
        else do
          let var' = unrename nameMap var
          illTyped $ "Type clash for variable " ++ var'
    Just (Left t') ->
        if t == t'
        then do
           k <- kindOf c
           return $ replace env var (Right (c `CPlus` COne k, t))
        else do
          let var' = unrename nameMap var
          illTyped $ "Type clash for variable " ++ var'
    Nothing -> return $ (var, Right (c, t)) : env

{- Helpers for error messages -}

unusedVariable :: String -> String
unusedVariable var = "Linear variable " ++ var ++ " was never used."
