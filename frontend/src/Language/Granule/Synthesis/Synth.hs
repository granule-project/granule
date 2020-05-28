{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
import Debug.Trace
import System.IO.Unsafe

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty

import Language.Granule.Context

-- import Language.Granule.Checker.Checker
import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Kinds (inferCoeffectType)
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables hiding (freshIdentifierBase)
import qualified Language.Granule.Checker.Variables as Var
import Language.Granule.Syntax.Span

import Data.List (delete)
import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except
import qualified Control.Monad.State.Strict as State (get, modify)
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Strict

import Language.Granule.Utils

data Configuration = Config
   { churchSyntax            :: Bool,
     howManyNatPossibilities :: Int
    }

freshIdentifierBase :: String -> Checker String
freshIdentifierBase s = do
  id <- Var.freshIdentifierBase s
  return $ delete '.' id

testVal :: (?globals :: Globals) => Bool
testVal  = do
  --addConstraint (ApproximatedBy nullSpanNoFile (CNat 0) (CZero $ zero (CNat 0) ) (zero (CNat 0)))
  case unsafePerformIO $ (evalChecker initState solve) of
    Left _ -> False
    Right x -> x
  -- where c = (CNat 1)


solve :: (?globals :: Globals)
  => Checker Bool
solve = do
  cs <- State.get
 -- newConjunct
  pred <- popFromPredicateStack
  traceM  ("pred: " <> pretty pred)
  -- let ctxtCk  = tyVarContext cs
--  coeffectVars <- justCoeffectTypesConverted nullSpanNoFile ctxtCk
  tyVars <- tyVarContextExistential >>= justCoeffectTypesConverted nullSpanNoFile
  result <- liftIO $ provePredicate pred tyVars
  case result of
    QED -> do
      traceM $ "yay"
      return True
    NotValid s -> do
      traceM ("message: " <> s)
      return False
    SolverProofError msgs -> do
      traceM $ ("message: " <> show msgs)
      return False
    OtherSolverError reason -> do
      traceM $ ("message: " <> show reason)
      return False
    Timeout -> do
      traceM "timed out"
      return False
    _ -> do
      return False
  where
    popFromPredicateStack = do
      st <- State.get
      return . head . predicateStack $ st

gradeAdd :: Coeffect -> Coeffect -> Maybe Coeffect
gradeAdd c c' = Just $ CPlus c c'

gradeSub :: Coeffect -> Coeffect -> Maybe Coeffect
gradeSub c c' =  Just $ CMinus c c'

gradeMult :: Coeffect -> Coeffect -> Maybe Coeffect
gradeMult c c' = Just $ CTimes c c'

gradeLub :: Coeffect -> Coeffect -> Maybe Coeffect
gradeLub c c' = Just $ CJoin c c'

gradeGlb :: Coeffect -> Coeffect -> Maybe Coeffect
gradeGlb c c' = Just $ CMeet c c'

ctxtSubtract :: Ctxt (Assumption)  -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
ctxtSubtract [] [] = Just []
ctxtSubtract ((x1, Linear t1):xs) ys =
  case lookup x1 ys of
    Just _ -> ctxtSubtract xs ys
    _ -> do
      ctx <- ctxtSubtract xs ys
      return $ (x1, Linear t1) : ctx
ctxtSubtract ((x1, Discharged t1 g1):xs) ys  =
  case lookup x1 ys of
    Just (Discharged t2 g2) ->
      case gradeSub g1 g2 of
        Just g3 -> do
          ctx <- ctxtSubtract xs ys
          return $ (x1, Discharged t1 g3):ctx
        Nothing -> Nothing
    _ -> do
      ctx <- ctxtSubtract xs ys
      return $ (x1, Discharged t1 g1):ctx
ctxtSubtract _ _ = Just []

ctxtMultByCoeffect :: Coeffect -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
ctxtMultByCoeffect _ [] = Just []
ctxtMultByCoeffect g1 ((x, Discharged t g2):xs) =
  case gradeMult g1 g2 of
    Just g' -> do
      ctxt <- ctxtMultByCoeffect g1 xs
      return $ ((x, Discharged t g'): ctxt)
    Nothing -> Nothing
ctxtMultByCoeffect _ _ = Nothing

ctxtMerge :: (Coeffect -> Coeffect -> Maybe Coeffect) -> Ctxt Assumption -> Ctxt Assumption -> Maybe (Ctxt Assumption)
ctxtMerge _ [] [] = Just []
ctxtMerge _ x [] = Just x
ctxtMerge _ [] y = Just y
ctxtMerge coefOp ((x, Discharged t1 g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Discharged t2 g2) ->
      if t1 == t2 then
        case coefOp g1 g2 of
          Just g3 -> do
            ctxt <- ctxtMerge coefOp xs ys'
            return $ (x, Discharged t1 g3) : ctxt
          Nothing -> Nothing
      else
        Nothing
    Nothing -> do
      ctxt <- ctxtMerge coefOp xs ys
      return $ (x, Discharged t1 g1) : ctxt
    _ -> Nothing
ctxtMerge coefOp ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> ctxtMerge coefOp xs ys
    Nothing -> Nothing
    _ -> Nothing

computeAddInputCtx :: Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption)
computeAddInputCtx gamma delta =
  case ctxtSubtract gamma delta of
    Just ctx' -> ctx'
    Nothing -> []

computeAddOutputCtx :: Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption)
computeAddOutputCtx del1 del2 del3 = do
  case ctxtAdd del1 del2 of
    Just del' ->
      case ctxtAdd del' del3 of
          Just del'' -> del''
          _ -> []
    _ -> []

ctxtAdd :: Ctxt Assumption -> Ctxt Assumption -> Maybe (Ctxt Assumption)
ctxtAdd [] [] = Just []
ctxtAdd x [] = Just x
ctxtAdd [] y = Just y
ctxtAdd ((x, Discharged t1 g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Discharged t2 g2) ->
      case gradeAdd g1 g2 of
        Just g3 -> do
          ctxt <- ctxtAdd xs ys'
          return $ (x, Discharged t1 g3) : ctxt
        Nothing -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Discharged t1 g1) : ctxt
    _ -> Nothing
ctxtAdd ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> ctxtAdd xs ys
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Linear t1) : ctxt
    _ -> Nothing

pattern ProdTy :: Type -> Type -> Type
pattern ProdTy t1 t2 = TyApp (TyApp (TyCon (Id "," ",")) t1) t2

pattern SumTy :: Type -> Type -> Type
pattern SumTy t1 t2  = TyApp (TyApp (TyCon (Id "Either" "Either")) t1) t2

isRAsync :: Type -> Bool
isRAsync (FunTy {}) = True
isRAsync _ = False

isLAsync :: Type -> Bool
isLAsync (ProdTy{}) = True
isLAsync (SumTy{}) = True
isLAsync (Box{}) = True
isLAsync _ = False

isAtomic :: Type -> Bool
isAtomic (FunTy {}) = False
isAtomic (ProdTy{}) = False
isAtomic (SumTy {}) = False
isAtomic (Box{}) = False
isAtomic (TyCon (Id "()" "()")) = False
isAtomic _ = True



newtype Synthesiser a = Synthesiser
  { unSynthesiser :: ExceptT (NonEmpty CheckerError) (StateT CheckerState (ListT IO)) a }
  deriving (Functor, Applicative, Monad)

instance MonadIO Synthesiser where
  liftIO = conv . liftIO

conv :: Checker a -> Synthesiser a
conv (Checker k) =  Synthesiser (ExceptT (StateT (\s -> ListT (fmap (\x -> [x]) $ runStateT (runExceptT k) s))))

tryAll :: Synthesiser a -> Synthesiser a -> Synthesiser a
tryAll m n =
  Synthesiser (ExceptT (StateT (\s -> mplus (runStateT (runExceptT (unSynthesiser n)) s) (runStateT (runExceptT (unSynthesiser m)) s))))

try :: Synthesiser a -> Synthesiser a -> Synthesiser a
try m n = tryAll m n

none :: Synthesiser a
none = Synthesiser (ExceptT (StateT (\s -> (ListT $ return []))))

data ResourceScheme = Additive | Subtractive
  deriving (Show, Eq)

testGlobals :: Globals
testGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }

-- ADTs available in synthesis (Either)
initDecls :: Ctxt (DataDecl)
initDecls =
  [
    (Id "Either" "Either", DataDecl
    {
      dataDeclSpan = nullSpanNoFile,
      dataDeclId = Id "Either" "Either",
      dataDeclTyVarCtxt = [((Id "a" "a"), KType),((Id "b" "b"), KType)],
      dataDeclKindAnn = Nothing,
      dataDeclDataConstrs =
        [
          DataConstrNonIndexed
          {
            dataConstrSpan = nullSpanNoFile,
            dataConstrId = (Id "Left" "Left"),
            dataConstrParams = [TyVar (Id "a" "a")]
          },
          DataConstrNonIndexed
          {
            dataConstrSpan = nullSpanNoFile,
            dataConstrId = (Id "Right" "Right"),
            dataConstrParams = [TyVar (Id "b" "b")]
          }
        ]
    })
  ]


testSyn :: Bool -> IO ()
testSyn useReprint =
  let ty =
--        FunTy Nothing (Box (CInterval (CNat 2) (CNat 3)) (TyVar $ mkId "b") ) (FunTy Nothing (SumTy (TyVar $ mkId "a") (TyVar $ mkId "c")) (SumTy (ProdTy (TyVar $ mkId "a") (Box (CInterval (CNat 2) (CNat 2)) (TyVar $ mkId "b") )) (ProdTy (TyVar $ mkId "c") (Box (CInterval (CNat 3) (CNat 3)) (TyVar $ mkId "b") ))))
--        FunTy Nothing (TyVar $ mkId "a") (SumTy (TyVar $ mkId "b") (TyVar $ mkId "a"))
--        FunTy Nothing (Box (CNat 3) (TyVar $ mkId "a")) (FunTy Nothing (Box (CNat 6) (TyVar $ mkId "b") ) (Box (CNat 3) (ProdTy (ProdTy (TyVar $ mkId "b") (TyVar $ mkId "b")) (TyVar $ mkId "a")) ))
--        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
--        FunTy Nothing (FunTy Nothing (TyVar $ mkId "a") (FunTy Nothing (TyVar $ mkId "b") (TyVar $ mkId "c"))) (FunTy Nothing (TyVar $ mkId "b") (FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "c")))
--        FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "a")
        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
        in
    let ts = (Forall nullSpanNoFile [(mkId "a", KType)] [] ty) in
    let ?globals = testGlobals in do
     -- State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) [(mkId "a", KType)]})
    let res = testOutput $ topLevel ts Subtractive in -- [(mkId "y", Linear (TyVar $ mkId "b")), (mkId "x", Linear (TyVar $ mkId "a"))] [] ty
        if length res == 0
        then  (putStrLn "No inhabitants found.")
        else  (forM_ res (\(ast, _, sub) -> putStrLn $
                           (if useReprint then pretty (reprintAsDef (mkId "f") ts ast) else pretty ast) ++ "\n" ++ (show sub) ))

testOutput :: Synthesiser (Expr () Type, Ctxt (Assumption), Substitution) -> [(Expr () Type, Ctxt (Assumption), Substitution)]
testOutput res =
  getList $ unsafePerformIO $ runListT $ evalStateT (runExceptT (unSynthesiser res)) initState

getList :: [Either (NonEmpty CheckerError) (Expr () Type, Ctxt Assumption, Substitution)] -> [(Expr () Type, Ctxt Assumption, Substitution)]
getList [] = []
getList (x:xs) = case x of
  Right x' -> x' : (getList xs)
  Left _ -> getList xs


topLevel :: (?globals :: Globals) => TypeScheme -> ResourceScheme -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
topLevel ts@(Forall _ binders constraints ty) resourceScheme = do
  conv $ State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) binders})
  synthesise initDecls True resourceScheme [] [] ts

-- Reprint Expr as a top-level declaration
reprintAsDef :: Id -> TypeScheme -> Expr () Type -> Def () Type
reprintAsDef id goalTy expr =
  refactorDef $
    Def
      { defSpan = nullSpanNoFile,
        defId = id,
        defRefactored = False,
        defEquations =
          EquationList
            { equationsSpan = nullSpanNoFile,
              equationsId = id,
              equationsRefactored = False,
              equations =
              [ Equation
                { equationSpan = nullSpanNoFile,
                  equationId = id,
                  equationRefactored = True,
                  equationAnnotation = getSecondParameter expr,
                  equationPatterns = [],
                  equationBody = expr
                }
              ]
            }
          ,
      defTypeScheme = goalTy
      }

-- Refactors a definition which contains abstractions in its equations
-- by pushing these abstractions into equation patterns
refactorDef :: Def () Type -> Def () Type
refactorDef (Def sp id ref (EquationList sp' id' ref' eqns) tyS) =
  Def sp id ref (EquationList sp' id' ref' (map refactorEqn eqns)) tyS

refactorEqn :: Equation v a -> Equation v a
refactorEqn (Equation sp name ref annotation pats body) =
  Equation sp name ref annotation (pats ++ getPatterns body) (exprBody body)
    where
      getPatterns e = boxPatterns e (exprPatterns e)

      replace (pat@(PVar _ _ _ name):xs) var pat' =
        if name == var then
          (pat' : (replace xs var pat'))
        else
          (pat : (replace xs var pat'))
      replace (pat@(PBox {}):xs) var pat' =
        pat : (replace xs var pat')
      replace ((PConstr s ty a id constrs):xs) var pat' =
        (PConstr s ty a id (replace constrs var pat')) : replace xs var pat'
      replace pats _ _ = pats

      exprPatterns (App _ _ _ (Val _ _ _ (Abs _ p _ e )) _) = exprPatterns e
      exprPatterns (Val _ _ _ (Abs _ p _ e)) = p  : exprPatterns e
      exprPatterns e = []

      boxPatterns (Val _ _ _ (Abs _ p _ e)) pats = boxPatterns e pats
      boxPatterns (App _ _ _ (Val _ _ _ (Abs _ p _ e )) (Val _ _ _ (Var _ name))) pats =
        boxPatterns e pats'
         where
          pats' = replace pats name p
      boxPatterns e pats = pats

      exprBody (App _ _ _ (Val _ _ _ (Abs _ _ _ e )) _) = exprBody e
      exprBody (Val _ _ _ (Abs _ _ _ e)) = exprBody e
      exprBody e = e

bindToContext :: (Id, Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> (Ctxt (Assumption), Ctxt (Assumption))
bindToContext var gamma omega True = (gamma, var:omega)
bindToContext var gamma omega False = (var:gamma, omega)


makeVar :: Id -> TypeScheme -> Expr () Type
makeVar name (Forall _ _ _ t) =
  Val s t False (Var t name)
  where s = nullSpanNoFile

makeAbs :: Id -> Expr () Type -> TypeScheme -> Expr () Type
makeAbs name e (Forall _ _ _ t@(FunTy _ t1 t2)) =
  Val s t False (Abs t (PVar s t False name) (Just t1) e)
  where s = nullSpanNoFile
makeAbs name e _ = error "Cannot synth here" -- TODO: better error handling

makeApp :: Id -> Expr () Type -> TypeScheme -> Type -> Expr () Type
makeApp name e (Forall _ _ _ t1) t2 =
  App s t1 False (makeVar name (Forall nullSpanNoFile [] [] t2)) e
  where s = nullSpanNoFile

makeBox :: TypeScheme -> Expr () Type -> Expr () Type
makeBox (Forall _ _ _ t) e =
  Val s t False (Promote t e)
  where s = nullSpanNoFile

makeUnbox :: Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makeUnbox name1 name2 (Forall _ _ _ goalTy) boxTy varTy e  =
  App s goalTy False
  (Val s boxTy False
    (Abs (FunTy Nothing boxTy goalTy)
      (PBox s boxTy False
        (PVar s varTy False name1)) (Just boxTy) e))
  (Val s varTy False
    (Var varTy name2))
  where s = nullSpanNoFile

makePair :: Type -> Type -> Expr () Type -> Expr () Type -> Expr () Type
makePair lTy rTy e1 e2 =
  App s rTy False (App s lTy False (Val s (ProdTy lTy rTy) False (Constr (ProdTy lTy rTy) (mkId ",") [])) e1) e2
  where s = nullSpanNoFile

makePairElim :: Id -> Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makePairElim name lId rId (Forall _ _ _ goalTy) lTy rTy e =
  App s goalTy False
  (Val s (ProdTy lTy rTy) False
    (Abs (FunTy Nothing (ProdTy lTy rTy) goalTy)
      (PConstr s (ProdTy lTy rTy) False (mkId ",") [(PVar s lTy False lId), (PVar s rTy False rId)] )
        Nothing e))
  (Val s (ProdTy lTy rTy) False (Var (ProdTy lTy rTy) name))
  where s = nullSpanNoFile

makeEitherLeft :: Type -> Type -> Expr () Type -> Expr () Type
makeEitherLeft lTy rTy e  =
  (App s lTy False (Val s (SumTy lTy rTy) False (Constr (SumTy lTy rTy) (mkId "Left") [])) e)
  where s = nullSpanNoFile

makeEitherRight :: Type -> Type -> Expr () Type -> Expr () Type
makeEitherRight lTy rTy e  =
  (App s rTy False (Val s (SumTy lTy rTy) False (Constr (SumTy lTy rTy) (mkId "Right") [])) e)
  where s = nullSpanNoFile

makeCase :: Type -> Type -> Id -> Id -> Id -> Expr () Type -> Expr () Type -> Expr () Type
makeCase t1 t2 sId lId rId lExpr rExpr =
  Case s (SumTy t1 t2) False (Val s (SumTy t1 t2) False (Var (SumTy t1 t2) sId)) [(PConstr s (SumTy t1 t2) False (mkId "Left") [(PVar s t1 False lId)], lExpr), (PConstr s (SumTy t1 t2) False (mkId "Right") [(PVar s t2 False rId)], rExpr)]
  where s = nullSpanNoFile

--makeEitherCase :: Id -> Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type
--makeEitherCase name lId rId (Forall _ _ _ goalTy) lTy rTy =

useVar :: (?globals :: Globals) => (Id, Assumption) -> Ctxt (Assumption) -> ResourceScheme -> Checker (Bool, Ctxt (Assumption), Type)
useVar (name, Linear t) gamma Subtractive = return (True, gamma, t)
useVar (name, Discharged t grade) gamma Subtractive = do
  (kind, _) <- inferCoeffectType nullSpan grade
  var <- freshTyVarInContext (mkId $ "c") (KPromote kind)
  existential var (KPromote kind)
  addConstraint (ApproximatedBy nullSpanNoFile (CPlus (CVar var) (COne kind)) grade kind)
  res <- solve
  case res of
    True -> do
      return (True, replace gamma name (Discharged t (CVar var)), t)
    False -> do
      return (False, [], t)
useVar (name, Linear t) _ Additive = return (True, [(name, Linear t)], t)
useVar (name, Discharged t grade) _ Additive = do
  (kind, _) <- inferCoeffectType nullSpan grade
  return (True, [(name, (Discharged t (COne kind)))], t)


varHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
varHelper decls left [] _ _ = none
varHelper decls left (var@(x, a) : right) resourceScheme goalTy =
  (varHelper decls (var:left) right resourceScheme goalTy) `try`
  do
    (canUse, gamma, t) <- conv $ useVar var (left ++ right) resourceScheme
    if canUse then
      case goalTy of
        Forall _ binders constraints goalTy' ->
          do
--            liftIO $ putStrLn $ "synth eq on (" <> pretty var <> ") " <> pretty t <> " and " <> pretty goalTy'
            (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile t goalTy'
            case success of
              True -> do
                return (makeVar x goalTy, gamma, subst)
              _ -> none
    else
      none

absHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> Bool
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
absHelper decls gamma omega allowLam resourceScheme goalTy =
  case goalTy of
      (Forall _ binders constraints (FunTy _ t1 t2)) -> do
        x <- conv $ freshIdentifierBase "x"
        let id = mkId x
        let (gamma', omega') =
              if isLAsync t1 then
                (gamma, ((id, Linear t1):omega))
              else
                (((id, Linear t1):gamma, omega))
        (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma' omega' (Forall nullSpanNoFile binders constraints t2)
        case (resourceScheme, lookupAndCutout id delta) of
          (Additive, Just (delta', Linear _)) ->
            return (makeAbs id e goalTy, delta', subst)
          (Subtractive, Nothing) ->
            return (makeAbs id e goalTy, delta, subst)
          _ -> none
      _ -> none


appHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
appHelper decls left [] _ _ = none
appHelper decls left (var@(x, a) : right) Subtractive goalTy@(Forall _ binders constraints _ ) =
  (appHelper decls (var : left) right Subtractive goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- conv $ useVar var omega Subtractive
  case (canUse, t) of
    (True, FunTy _ t1 t2) -> do
        id <- conv $ freshIdentifierBase "x"
        let id' = mkId id
        let (gamma', omega'') = bindToContext (id', Linear t2) omega' [] (isLAsync t2)
        (e1, delta1, sub1) <- synthesiseInner decls True Subtractive gamma' omega'' goalTy
        (e2, delta2, sub2) <- synthesiseInner decls True Subtractive delta1 [] (Forall nullSpanNoFile binders constraints t1)
        subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
        case lookup id' delta2 of
          Nothing ->
            return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id' e1, delta2, subst)
          _ -> none
    _ -> none
appHelper decls left (var@(x, a) : right) Additive goalTy@(Forall _ binders constraints _ ) =
  (appHelper decls (var : left) right Additive goalTy) `try`
  let omega = left ++ right in do
    (canUse, omega', t) <- conv $ useVar var omega Additive
    case (canUse, t) of
      (True, FunTy _ t1 t2) -> do
        id <- conv $ freshIdentifierBase "x"
        let id' = mkId id
        let gamma1 = computeAddInputCtx omega omega'
        let (gamma1', omega'') = bindToContext (id', Linear t2) gamma1 [] (isLAsync t2)
        (e1, delta1, sub1) <- synthesiseInner decls True Additive gamma1' omega'' goalTy

        let gamma2 = computeAddInputCtx gamma1' delta1
        (e2, delta2, sub2) <- synthesiseInner decls True Additive gamma2 [] (Forall nullSpanNoFile binders constraints t1)

        let delta3 = computeAddOutputCtx omega' delta1 delta2
        subst <- conv $ combineSubstitutions nullSpan sub1 sub2
        case lookupAndCutout id' delta3 of
          Just (delta3', Linear _) ->
                return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id' e1, delta3', subst)
          _ -> none
      _ -> none


boxHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
boxHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (Box g t)) -> do
      (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t)
      case resourceScheme of
        Additive ->
          case ctxtMultByCoeffect g delta of
            Just delta' -> do
              return (makeBox goalTy e, delta', subst)
            _ -> none
        Subtractive ->
          let used = ctxtSubtract gamma delta in
            -- Compute what was used to synth e
            case used of
              Just used' -> do
                case ctxtMultByCoeffect g used' of
                  Just delta' -> do
                    case ctxtSubtract gamma delta' of
                      Just delta'' -> do
                        return (makeBox goalTy e, delta'', subst)
                      Nothing -> none
                  _ -> none
              _ -> none
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
unboxHelper decls left [] _ _ _ = none
unboxHelper decls left (var@(x, a) : right) gamma Subtractive goalTy =
    let omega = left ++ right in do
      (canUse, omega', t) <- conv $ useVar var omega Subtractive
      case (canUse, t) of
        (True, Box grade t') -> do
          id <- conv $ freshIdentifierBase "x"
          let id' = mkId id
          let (gamma', omega'') = bindToContext (id', Discharged t' grade) gamma omega' (isLAsync t')
          (e, delta, subst) <- synthesiseInner decls True Subtractive gamma' omega'' goalTy
          case lookupAndCutout id' delta of
            Just (delta', (Discharged _ usage)) -> do
              (kind, _) <- conv $ inferCoeffectType nullSpan usage
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (CZero kind) usage kind)
              res <- conv $ solve
              case res of
                True ->
                  return (makeUnbox id' x goalTy t t' e, delta', subst)
                False -> do
                  none
            _ -> none
        _ -> none
    `try `(unboxHelper decls (var : left) right gamma Subtractive goalTy)
unboxHelper decls left (var@(x, a) : right) gamma Additive goalTy =
    (unboxHelper decls (var : left) right gamma Additive goalTy) `try`
    let omega = left ++ right in do
      (canUse, omega', t) <- conv $ useVar var omega Additive
      case (canUse, t) of
        (True, Box grade t') -> do
           id <- conv $ freshIdentifierBase "x"
           let id' = mkId id
           let omega1 = computeAddInputCtx omega omega'
           let (gamma', omega1') = bindToContext (id', Discharged t' grade) gamma omega1 (isLAsync t')
           (e, delta, subst) <- synthesiseInner decls True Additive gamma' omega1' goalTy
           let delta' = computeAddOutputCtx omega' delta []
           case lookupAndCutout id' delta' of
             Just (delta'', (Discharged _ usage)) -> do
               (kind, _) <- conv $ inferCoeffectType nullSpan grade
               conv $ addConstraint (Eq nullSpanNoFile grade usage kind)
               res <- conv $ solve
               case res of
                 True ->
                   return (makeUnbox id' x goalTy t t' e,  delta'', subst)
                 False -> none
             _ -> do
               (kind, _) <- conv $ inferCoeffectType nullSpan grade
               conv $ addConstraint (ApproximatedBy nullSpanNoFile grade (CZero kind) kind)
               res <- conv $ solve
               case res of
                 True ->
                   return (makeUnbox id' x goalTy t t' e,  delta', subst)
                 False -> none
        _ -> none


pairElimHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
pairElimHelper decls left [] _ _ _ = none
pairElimHelper decls left (var@(x, a):right) gamma Subtractive goalTy =
  (pairElimHelper decls (var:left) right gamma Subtractive goalTy) `try`
  let omega = left ++ right in do
    (canUse, omega', t) <- conv $ useVar var omega Subtractive
    case (canUse, t) of
      (True, ProdTy t1 t2) -> do
          l <- conv $ freshIdentifierBase "x"
          r <- conv $ freshIdentifierBase "x"
          let (lId, rId) = (mkId l, mkId r)
          let (gamma', omega'') = bindToContext (lId, Linear t1) gamma omega' (isLAsync t1)
          let (gamma'', omega''') = bindToContext (rId, Linear t2) gamma' omega'' (isLAsync t2)
          (e, delta, subst) <- synthesiseInner decls True Subtractive gamma'' omega''' goalTy
          case (lookup lId delta, lookup rId delta) of
            (Nothing, Nothing) -> return (makePairElim x lId rId goalTy t1 t2 e, delta, subst)
            _ -> none
      _ -> none
pairElimHelper decls left (var@(x, a):right) gamma Additive goalTy =
  (pairElimHelper decls (var:left) right gamma Additive goalTy) `try`
  let omega = left ++ right in do
    (canUse, omega', t) <- conv $ useVar var omega Additive
    case (canUse, t) of
      (True, ProdTy t1 t2) -> do
          l <- conv $ freshIdentifierBase "x"
          r <- conv $ freshIdentifierBase "x"
          let (lId, rId) = (mkId l, mkId r)
          let omega1 = computeAddInputCtx omega omega'
          let (gamma', omega1') = bindToContext (lId, Linear t1) gamma omega1 (isLAsync t1)
          let (gamma'', omega1'') = bindToContext (rId, Linear t2) gamma' omega1' (isLAsync t2)
          (e, delta, subst) <- synthesiseInner decls True Additive gamma'' omega1'' goalTy
          let delta' = computeAddOutputCtx omega' delta []
          case lookupAndCutout lId delta' of
            Just (delta', Linear _) ->
              case lookupAndCutout rId delta' of
                Just (delta''', Linear _) -> return (makePairElim x lId rId goalTy t1 t2 e, delta''', subst)
                _ -> none
            _ -> none
      _ -> none

unitIntroHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
unitIntroHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (TyCon (internalName -> "()"))) -> do
      let unitVal = Val nullSpan (TyCon (mkId "()")) True
                      (Constr (TyCon (mkId "()")) (mkId "()") [])
      case resourceScheme of
        Additive -> return (unitVal, [], [])
        Subtractive -> return (unitVal, gamma, [])
    _ -> none

pairIntroHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
pairIntroHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (ProdTy t1 t2)) -> do
      --liftIO $ putStrLn "Doing pair intro helper"
      --liftIO $ putStrLn $ show gamma
      (e1, delta1, subst1) <- synthesiseInner decls True resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t1)
      let gamma2 = if resourceScheme == Additive then computeAddInputCtx gamma delta1 else delta1
      (e2, delta2, subst2) <- synthesiseInner decls True resourceScheme gamma2 [] (Forall nullSpanNoFile binders constraints t2)
      let delta3 = if resourceScheme == Additive then computeAddOutputCtx delta1 delta2 [] else delta2
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta3, subst)
    _ -> none


sumIntroHelper :: (?globals :: Globals)
  => Ctxt (DataDecl) -> Ctxt (Assumption) -> ResourceScheme -> TypeScheme -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
sumIntroHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (SumTy t1 t2)) -> do
      try
        (do
            (e1, delta1, subst1) <- synthesiseInner decls True resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t1)
            return (makeEitherLeft t1 t2 e1, delta1, subst1)

        )
        (do
            (e2, delta2, subst2) <- synthesiseInner decls True resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t2)
            return (makeEitherRight t1 t2 e2, delta2, subst2)

        )
    _ -> none


sumElimHelper :: (?globals :: Globals)
  => Ctxt (DataDecl)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> Ctxt (Assumption)
  -> ResourceScheme
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
sumElimHelper decls left [] _ _ _ = none
sumElimHelper decls left (var@(x, a):right) gamma Subtractive goalTy =
  (sumElimHelper decls (var:left) right gamma Subtractive goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- conv $ useVar var omega Subtractive
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      freshL <- conv $ freshIdentifierBase "x"
      freshR <- conv $ freshIdentifierBase "x"
      let l = mkId freshL
      let r = mkId freshR
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma' omega'' (isLAsync t2)
      (e1, delta1, subst1) <- synthesiseInner decls True Subtractive gamma' omega'' goalTy
      (e2, delta2, subst2) <- synthesiseInner decls True Subtractive gamma'' omega''' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookup l delta1, lookup r delta2) of
          (Nothing, Nothing) ->
            case ctxtMerge gradeGlb delta1 delta2 of
              Just delta3 ->
                return (makeCase t1 t2 x l r e1 e2, delta3, subst)
              Nothing -> none
          _ -> none
    _ -> none

sumElimHelper decls left (var@(x, a):right) gamma Additive goalTy =
  (sumElimHelper decls (var:left) right gamma Additive goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- conv $ useVar var omega Additive
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      freshL <- conv $ freshIdentifierBase "x"
      freshR <- conv $ freshIdentifierBase "x"
      let l = mkId freshL
      let r = mkId freshR
      let omega1 = computeAddInputCtx omega omega'
      let (gamma', omega1') = bindToContext (l, Linear t1) gamma omega1 (isLAsync t1)
      let (gamma'', omega1'') = bindToContext (r, Linear t2) gamma' omega1' (isLAsync t2)
      (e1, delta1, subst1) <- synthesiseInner decls True Additive gamma' omega1' goalTy
      (e2, delta2, subst2) <- synthesiseInner decls True Additive gamma'' omega1'' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookupAndCutout l delta1, lookupAndCutout r delta2) of
          (Just (delta1', Linear _), Just (delta2', Linear _)) ->
            case ctxtMerge gradeLub delta1' delta2' of
              Just delta3 ->
                let delta3' = computeAddOutputCtx omega' delta3 [] in do
                   return (makeCase t1 t2 x l r e1 e2, delta3', subst)
              Nothing -> none
          _ -> none
    _ -> none



synthesiseInner :: (?globals :: Globals)
           => Ctxt (DataDecl)      -- ADT Definitions
           -> Bool                 -- whether a function is allowed at this point
           -> ResourceScheme       -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption)    -- (unfocused) free variables
           -> Ctxt (Assumption)    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)

synthesiseInner decls allowLam resourceScheme gamma omega goalTy@(Forall _ binders _ goalTy') =
  case (isRAsync goalTy', omega) of
    (True, omega) ->
      -- Right Async : Decompose goalTy until synchronous
      absHelper decls gamma omega allowLam resourceScheme goalTy `try` none
    (False, omega@(x:xs)) ->
      -- Left Async : Decompose assumptions until they are synchronous (eliminators on assumptions)
      unboxHelper decls [] omega gamma resourceScheme goalTy
      `try`
      (pairElimHelper decls [] omega gamma resourceScheme goalTy
      `try`
      sumElimHelper decls [] omega gamma resourceScheme goalTy)
    (False, []) ->
      -- Transition to synchronous (focused) search
      if isAtomic goalTy' then
        -- Left Sync: App rule + Init rules
        varHelper decls [] gamma resourceScheme goalTy
        `try`
        appHelper decls [] gamma resourceScheme goalTy
      else
        -- Right Sync : Focus on goalTy
        (sumIntroHelper decls gamma resourceScheme goalTy
        `try`
        pairIntroHelper decls gamma resourceScheme goalTy)
        `try`
        boxHelper decls gamma resourceScheme goalTy
        `try`
        unitIntroHelper decls gamma resourceScheme goalTy

synthesise :: (?globals :: Globals)
           => Ctxt (DataDecl)      -- ADT Definitions
           -> Bool                 -- whether a function is allowed at this point
           -> ResourceScheme       -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption)    -- (unfocused) free variables
           -> Ctxt (Assumption)    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
synthesise decls allowLam resourceScheme gamma omega goalTy = do
  result@(expr, ctxt, subst) <- synthesiseInner decls allowLam resourceScheme gamma omega goalTy
  case resourceScheme of
    Subtractive -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, a) -> conv $
                    case a of
                      Linear{} -> return False;
                      Discharged _ grade -> do
                        (kind, _) <- inferCoeffectType nullSpan grade
                        addConstraint (ApproximatedBy nullSpanNoFile (CZero kind) grade kind)
                        solve) ctxt
      if and consumed
        then return result
        else none

    Additive -> do
      consumed <- mapM (\(id, a) -> conv $
                    case lookup id gamma of
                      Just (Linear{}) -> return True;
                      Just (Discharged _ grade) ->
                        case a of
                          Discharged _ grade' -> do
                            (kind, _) <- inferCoeffectType nullSpan grade
                            addConstraint (ApproximatedBy nullSpanNoFile grade' grade kind)
                            solve
                          _ -> return False
                      Nothing -> return False) ctxt
      if and consumed
        then return result
        else none

