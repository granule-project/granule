{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
import Debug.Trace
import System.IO.Unsafe

--import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
--import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Context
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables
import Language.Granule.Syntax.Span

import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Strict

import Language.Granule.Utils

data Configuration = Config
   { churchSyntax            :: Bool,
     howManyNatPossibilities :: Int
    }

canUse :: Coeffect -> Bool
canUse (CNat n) = (n > 0)
canUse (CInterval (CNat _) (CNat n2)) = (n2 > 0)
canUse (CInfinity _) = True
canUse _ = False

zeroUse :: Coeffect -> Bool
zeroUse (CNat n) = (n == 0)
zeroUse (CInterval (CNat n1) (CNat _)) = (n1 == 0)
zeroUse (CInfinity _) = True
zeroUse _ = False

useCoeffect :: Coeffect -> Maybe Coeffect
useCoeffect (CNat n) = Just $ CNat (n - 1)
useCoeffect (CInterval (CNat n1) (CNat n2)) = Just $ CInterval (CNat (n1 `monus` 1)) (CNat (n2-1))
  where
    monus 0 x = 0
    monus x y = x - y
useCoeffect (CInfinity t) = Just $ CInfinity t
useCoeffect _ = Nothing

checkSubUsage :: Coeffect -> Bool
checkSubUsage (CNat n1) = not (canUse $ CNat n1)
checkSubUsage (CInterval (CNat n1) _) = n1 == 0
checkSubUsage (CInfinity _) = True
checkSubUsage _ = False

checkAddUsage :: Coeffect -> Coeffect -> Bool
checkAddUsage (CNat n1) (CNat n2) = n1 == n2
checkAddUsage (CInterval (CNat n1) (CNat n2)) (CInterval (CNat n1') (CNat n2')) =
  n1 >= n1' && n2 <= n2' && n1 <= n2 && n1' <= n2'
checkAddUsage (CInfinity t1) (CInfinity t2) = t1 == t2
checkAddUsage _ _ = False


gradeAdd :: Coeffect -> Coeffect -> Maybe Coeffect
gradeAdd (CNat n) (CNat n') = Just $ CNat (n + n')
gradeAdd (CInterval (CNat n1) (CNat n2)) (CInterval (CNat n1') (CNat n2')) =
  let (n3, n4) = (n1 + n1', n2 + n2') in
  Just $ CInterval (CNat n3) (CNat n4)
gradeAdd (CInfinity t1) (CInfinity t2) = Just $ CInfinity t1
gradeAdd _ _ = Nothing

gradeSub :: Coeffect -> Coeffect -> Maybe Coeffect
gradeSub (CNat n) (CNat n') = if n - n' < 0 then Nothing else Just $ CNat (n - n')
gradeSub (CInterval (CNat n1) (CNat n2)) (CInterval (CNat n1') (CNat n2')) =
  let (n3, n4) = if n1' == 0 then
        (n2 - n2', n2 - n2')
        else
        (n1 - n1', n2 - n2') in
    case (n3<0, n4<0) of
      (True, False)-> Just $ (CInterval (CNat 0) (CNat n4))
      (False, False)-> Just $ (CInterval (CNat n3) (CNat n4))
      _ -> Nothing
gradeSub (CInfinity t1) (CInfinity t2) = Just (CInfinity t1)
gradeSub _ _ = Nothing

gradeMult :: Coeffect -> Coeffect -> Maybe Coeffect
gradeMult (CNat n) (CNat n') = Just $ CNat (n * n')
gradeMult (CInterval (CNat n1) (CNat n2)) (CInterval (CNat n1') (CNat n2')) =
  let (n3, n4) =
        (n1 * n1', n2 * n2') in
    Just $ (CInterval (CNat n3) (CNat n4))
gradeMult (CInfinity t1) (CInfinity t2) = Just $ CInfinity t1
gradeMult _ _ = Nothing

ctxSubtract :: Ctxt (Assumption)  -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
ctxSubtract [] [] = Just []
ctxSubtract ((x1, Linear t1):xs) ys =
  case lookup x1 ys of
    Just _ -> ctxSubtract xs ys
    _ -> do
      ctx <- ctxSubtract xs ys
      return $ (x1, Linear t1) : ctx
ctxSubtract ((x1, Discharged t1 g1):xs) ys  =
  case lookup x1 ys of
    Just (Discharged t2 g2) ->
      case gradeSub g1 g2 of
        Just g3 -> do
          ctx <- ctxSubtract xs ys
          return $ (x1, Discharged t1 g3):ctx
        Nothing -> Nothing
    _ -> do
      ctx <- ctxSubtract xs ys
      return $ (x1, Discharged t1 g1):ctx
ctxSubtract _ _ = Just []

ctxMultByCoeffect :: Ctxt (Assumption) -> Coeffect -> Maybe (Ctxt (Assumption))
ctxMultByCoeffect [] _ = Just []
ctxMultByCoeffect ((x, Discharged t1 g1):xs) g2 =
  case gradeMult g1 g2 of
    Just g3 -> do
      ctxt <- ctxMultByCoeffect xs g2
      return $ ((x, Discharged t1 g3): ctxt)
    Nothing -> Nothing
ctxMultByCoeffect _ _ = Nothing

gradeLub :: Coeffect -> Coeffect -> Maybe Coeffect
gradeLub (CInterval (CNat g1) (CNat g2)) (CInterval (CNat g1') (CNat g2')) =
  Just (CInterval (CNat (min g1 g1')) (CNat (max g2 g2')))
gradeLub (CNat n) (CNat n') = if n == n' then Just (CNat n) else Nothing
gradeLub (CInfinity t1) (CInfinity t2) = Just (CInfinity t1)
gradeLub _ _ = Nothing

gradeGlb :: Coeffect -> Coeffect -> Maybe Coeffect
gradeGlb (CInterval (CNat g1) (CNat g2)) (CInterval (CNat g1') (CNat g2')) = Just (CInterval (CNat (max g1 g1')) (CNat (min g2 g2')))
gradeGlb (CNat n) (CNat n') = if n == n' then Just (CNat n) else Nothing
gradeGlb (CInfinity t1) (CInfinity t2) = Just $ CInfinity t1
gradeGlb _ _ = Nothing

ctxGlb :: Ctxt (Assumption) -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
ctxGlb [] [] = Just []
ctxGlb x [] = Just x
ctxGlb [] y = Just y
ctxGlb ((x, Discharged t1 g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Discharged t2 g2) ->
      if t1 == t2 then
        case gradeGlb g1 g2 of
          Just g3 -> do
            ctx <- ctxGlb xs ys'
            return $ (x, Discharged t1 g3) : ctx
          Nothing -> Nothing
      else
        Nothing
    Nothing -> do
      ctx <- ctxGlb xs ys
      return $ (x, Discharged t1 g1) : ctx
    _ -> Nothing
ctxGlb ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> ctxGlb xs ys
    Nothing -> Nothing
    _ -> Nothing

ctxLub :: Ctxt (Assumption) -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
ctxLub [] [] = Just []
ctxLub x [] = Just x
ctxLub [] y = Just y
ctxLub ((x, Discharged t1 g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Discharged t2 g2) ->
      if t1 == t2 then
        case gradeLub g1 g2 of
          Just g3 -> do
            ctx <- ctxLub xs ys'
            return $ (x, Discharged t1 g3) : ctx
          Nothing -> Nothing
      else
        Nothing
    Nothing -> do
      ctx <- ctxLub xs ys
      return $ (x, Discharged t1 g1) : ctx
    _ -> Nothing
ctxLub ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> ctxLub xs ys
    Nothing -> Nothing
    _ -> Nothing

checkCtxApproximation :: Ctxt (Assumption) -> Ctxt (Assumption) -> Maybe (Ctxt (Assumption))
checkCtxApproximation [] _ = return []
checkCtxApproximation ((x, Discharged t1 g1):xs) ys =
  case lookup x ys of
    Just (Discharged t2 g2) ->
        if g1 <= g2 then do
            ctxt <- checkCtxApproximation xs ys
            return $ (x, Discharged t1 g1) : ctxt
        else Nothing
    _ -> Nothing
checkCtxApproximation _ ys = Nothing

computeAddInputCtx :: Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption)
computeAddInputCtx gamma delta =
  case ctxSubtract gamma delta of
    Just ctx' -> ctx'
    Nothing -> []

computeAddOutputCtx :: Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption)
computeAddOutputCtx del1 del2 del3 = do
  case addDeltas del1 del2 of
    Just del' ->
      case addDeltas del' del3 of
          Just del'' -> del''
          _ -> []
    _ -> []
  where
  addDeltas [] [] = Just []
  addDeltas x [] = Just x
  addDeltas [] y = Just y
  addDeltas ((x, Discharged t1 g1):xs) ys =
    case lookupAndCutout x ys of
      Just (ys', Discharged t2 g2) ->
        case gradeAdd g1 g2 of
          Just g3 -> do
            ctxt <- addDeltas xs ys'
            return $ (x, Discharged t1 g3) : ctxt
          Nothing -> Nothing
      Nothing -> do
        ctxt <- addDeltas xs ys
        return $ (x, Discharged t1 g1) : ctxt
      _ -> Nothing
  addDeltas ((x, Linear t1):xs) ys =
    case lookup x ys of
      Just (Linear t2) -> addDeltas xs ys
      Nothing -> do
        ctxt <- addDeltas xs ys
        return $ (x, Linear t1) : ctxt
      _ -> Nothing


isRAsync :: Type -> Bool
isRAsync (FunTy {}) = True
isRAsync _ = False

isLAsync :: Type -> Bool
isLAsync (TyApp (TyApp (TyCon (Id "," ",")) _) _) = True -- ProdTy
--isLAsync (SumTy{}) = True
isLAsync (Box{}) = True
isLAsync _ = False

isAtomic :: Type -> Bool
isAtomic (FunTy {}) = False
isAtomic (TyApp (TyApp (TyCon (Id "," ",")) _) _) = False -- ProdTy
--isAtomic (SumTy {}) = False
isAtomic (Box{}) = False
isAtomic _ = True

newtype Synthesiser a = Synthesiser
  { unSynthesiser :: ExceptT (NonEmpty CheckerError) (StateT CheckerState (ListT IO)) a }
  deriving (Functor, Applicative, Monad)
conv :: Checker a -> Synthesiser a
conv (Checker k) =  Synthesiser (ExceptT (StateT (\s -> ListT (fmap (\x -> [x]) $ runStateT (runExceptT k) s))))

tryAll :: Synthesiser a -> Synthesiser a -> Synthesiser a
tryAll m n =
  Synthesiser (ExceptT (StateT (\s -> mplus (runStateT (runExceptT (unSynthesiser n)) s) (runStateT (runExceptT (unSynthesiser m)) s))))

try :: Synthesiser a -> Synthesiser a -> Synthesiser a
try m n = tryAll m n

none :: Synthesiser a
none = Synthesiser (ExceptT (StateT (\s -> (ListT $ return []))))



testGlobals :: Globals
testGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }


testSyn :: IO ()
testSyn =
  let ty =

-- FunTy (FunTy (PVar "a") (FunTy (PVar "b") (PVar "c"))) (FunTy (PVar "b") (FunTy (PVar "a") (PVar "c")))

        FunTy Nothing (FunTy Nothing (TyVar $ mkId "a") (FunTy Nothing (TyVar $ mkId "b") (TyVar $ mkId "c"))) (FunTy Nothing (TyVar $ mkId "b") (FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "c")))

       -- TyVar $ mkId "a"
        in
    let ?globals = testGlobals in
    let res = testOutput $ synthesise True False [] [] ty in -- [(mkId "y", Linear (TyVar $ mkId "b")), (mkId "x", Linear (TyVar $ mkId "a"))] [] ty
      if length res == 0
      then putStrLn "No inhabitants found."
      else forM_ res (\(ast, _, sub) -> putStrLn $ (pretty ty) ++ "\n" ++ pretty ast ++ "\n" ++ (show sub) )

testOutput :: Synthesiser (Expr () Type, Ctxt (Assumption), Substitution) -> [(Expr () Type, Ctxt (Assumption), Substitution)]
testOutput res =
  getList $ unsafePerformIO $ runListT $ evalStateT (runExceptT (unSynthesiser res)) initState

getList :: [Either (NonEmpty CheckerError) (Expr () Type, Ctxt Assumption, Substitution)] -> [(Expr () Type, Ctxt Assumption, Substitution)]
getList [] = []
getList (x:xs) = case x of
  Right x' -> x' : (getList xs)
  Left _ -> getList xs


bindToContext :: (Id, Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> (Ctxt (Assumption), Ctxt (Assumption))
bindToContext var gamma omega True = (gamma, var:omega)
bindToContext var gamma omega False = (var:gamma, omega)

useVar :: (Id, Assumption) -> Ctxt (Assumption) -> Bool -> (Bool, Ctxt (Assumption), Type)
useVar (name, Linear t) gamma False = (True, gamma, t)
useVar (name, Discharged t grade) gamma False =
    if canUse grade then
      case useCoeffect grade of
        Nothing -> (False, [], t )
        Just grade' ->
          (True, (name, Discharged t grade'):gamma, t)
    else
        (False, [], t)
useVar (name, Linear t) _ True = (True, [(name, Linear t)], t)
useVar (name, Discharged t grade) _ True =
    if canUse grade then
      case useCoeffect grade of
        Nothing -> (False, [], t)
        Just grade' ->
          let singleUse = gradeSub grade grade' in
            case singleUse of
              Just grade'' -> (True, [(name, Discharged t grade'')], t)
              Nothing -> (False, [], t)
    else
        (False, [], t)

makeVar :: Id -> Type -> Expr () Type
makeVar name t =
  Val nullSpanNoFile t False (Var t name)

makeAbs :: Id -> Expr () Type -> Type -> Expr () Type
makeAbs name e t =
  Val nullSpanNoFile t False (Abs t (PVar nullSpanNoFile t False name) Nothing e)

makeApp :: Id -> Expr () Type -> Type -> Type -> Expr () Type
makeApp name e t1 t2 =
  App nullSpanNoFile t1 False (makeVar name t2) e

makeBox :: Type -> Expr () Type -> Expr () Type
makeBox t e =
  Val (nullSpanNoFile) t False (Promote t e)

makeUnbox :: Id -> Id -> Type -> Type -> Type -> Expr () Type -> Expr () Type
makeUnbox name1 name2 goalTy boxTy varTy e  =
  App (nullSpanNoFile) goalTy False
  (Val (nullSpanNoFile) boxTy False
    (Abs (FunTy Nothing boxTy goalTy)
      (PBox (nullSpanNoFile) varTy False
        (PVar (nullSpanNoFile) varTy False name1)) Nothing e))
  (Val (nullSpanNoFile) varTy False
    (Var varTy name2))

varHelper :: (?globals :: Globals)
  => Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> Type -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
varHelper left [] _ _ = none
varHelper left (var@(x, a) : right) isAdd goalTy =
  (varHelper (var:left) right isAdd goalTy) `try`
  let (canUse, gamma, t) = useVar var (left ++ right) isAdd in
    if canUse then
      do
        subst <- conv $ unify goalTy t
        case subst of
          Just sub' -> return (makeVar x goalTy, gamma, sub')
          _ -> none
    else
      none

absHelper :: (?globals :: Globals)
  => Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> Bool -> Type -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
absHelper gamma omega allowLam isAdd goalTy =
  case goalTy of
      FunTy _ t1 t2 -> do
        x <- conv $ freshIdentifierBase "x"
        let id = mkId x
        let (gamma', omega') =
              if isLAsync t1 then
                (gamma, ((id, Linear t1):omega))
              else
                (((id, Linear t1):gamma, omega))
        (e, delta, subst) <- synthesise True isAdd gamma' omega' t2
        case (isAdd, lookupAndCutout id delta) of
          (True, Just (delta', Linear _)) ->
            return (makeAbs id e goalTy, delta', subst)
          (False, Nothing) ->
            return (makeAbs id e goalTy, delta, subst)
          _ -> none
      _ -> none


appHelper :: (?globals :: Globals)
  => Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> Type -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
appHelper left [] _ _ = none
appHelper left (var@(x, a) : right) False goalTy =
  (appHelper (var : left) right False goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega False in
  case (canUse, t) of
    (True, FunTy _ t1 t2) -> do
        id <- conv $ freshIdentifierBase "x"
        let id' = mkId id
        let (gamma', omega'') = bindToContext (id', Linear t2) omega' [] (isLAsync t2)
        (e1, delta1, sub1) <- synthesise True False gamma' omega'' goalTy
        (e2, delta2, sub2) <- synthesise True False delta1 [] t1
        subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
        case lookup id' delta2 of
          Nothing ->
            return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id' e1, delta2, subst)
          _ -> none
    _ -> none
appHelper left (var@(x, a) : right) True goalTy =
  (appHelper (var : left) right True goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega True in
    case (canUse, t) of
      (True, FunTy _ t1 t2) -> do
        id <- conv $ freshIdentifierBase "x"
        let id' = mkId id
        let gamma1 = computeAddInputCtx omega omega'
        let (gamma1', omega'') = bindToContext (id', Linear t2) gamma1 [] (isLAsync t2)
        (e1, delta1, sub1) <- synthesise True True gamma1' omega'' goalTy

        let gamma2 = computeAddInputCtx gamma1' delta1
        (e2, delta2, sub2) <- synthesise True True gamma2 [] t1

        let delta3 = computeAddOutputCtx omega' delta1 delta2
        subst <- conv $ combineSubstitutions nullSpan sub1 sub2
        case lookupAndCutout id' delta3 of
          Just (delta3', Linear _) ->
                return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id' e1, delta3', subst)
          _ -> none
      _ -> none

boxHelper :: (?globals :: Globals)
  => Ctxt (Assumption) -> Bool -> Type -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
boxHelper gamma False goalTy =
  case goalTy of
    Box g t -> do
      (e, delta, subst) <- synthesise True False gamma [] t
      let used = ctxSubtract gamma delta in
        -- Compute what was used to synth e
        case used of
          Just used' -> do
            case ctxMultByCoeffect used' g of
              Just delta' -> do
                case ctxSubtract gamma delta' of
                  Just delta'' -> do
                    return (makeBox goalTy e, delta'', subst)
                  Nothing -> none
              _ -> none
          _ -> none
    _ -> none

boxHelper gamma True goalTy =
  case goalTy of
    Box g t -> do
      (e, delta, subst) <- synthesise True True gamma [] t
      case ctxMultByCoeffect delta g of
        Just delta' -> do
            return (makeBox goalTy e, delta', subst)
        _ -> none
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Ctxt (Assumption) -> Ctxt (Assumption) -> Ctxt (Assumption) -> Bool -> Type -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)
unboxHelper left [] _ _ _ = none
unboxHelper left (var@(x, a) : right) gamma False goalTy =
    (unboxHelper (var : left) right gamma False goalTy) `try`
    let omega = left ++ right in
    let (canUse, omega', t) = useVar var omega False in
      case (canUse, t) of
        (True, Box grade t') -> do
          id <- conv $ freshIdentifierBase "x"
          let id' = mkId id
          let (gamma', omega'') = bindToContext (id', Discharged t' grade) gamma omega' (isLAsync t')
          (e, delta, subst) <- synthesise True False gamma' omega'' goalTy
          case lookupAndCutout id' delta of
            Just (delta', (Discharged _ usage)) ->
              if checkSubUsage usage then
                return (makeUnbox id' x goalTy t t' e, delta', subst)
              else
                none
            _ -> none
        _ -> none
unboxHelper left (var@(x, a) : right) gamma True goalTy =
    (unboxHelper (var : left) right gamma True goalTy) `try`
    let omega = left ++ right in
    let (canUse, omega', t) = useVar var omega True in
      case (canUse, t) of
        (True, Box grade t') -> do
           id <- conv $ freshIdentifierBase "x"
           let id' = mkId id
           let omega1 = computeAddInputCtx omega omega'
           let (gamma', omega1') = bindToContext (id', Discharged t' grade) gamma omega1 (isLAsync t')
           (e, delta, subst) <- synthesise True True gamma' omega1' goalTy
           let delta' = computeAddOutputCtx omega' delta []
           case lookupAndCutout id' delta' of
             Just (delta'', (Discharged _ usage)) ->
               if checkAddUsage usage grade then
                 return (makeUnbox id' x goalTy t t' e,  delta'', subst)
               else
                 none
             _ ->
               if zeroUse grade then
                 return (makeUnbox id' x goalTy t t' e,  delta', subst)
               else none
        _ -> none

{-
natIntroHelper :: (?configuration :: Configuration)
  => Context -> Bool -> Type -> StateT Int [] (Expr PCF, Context, Substitution)
natIntroHelper gamma isAdditive goalTy =
  case goalTy of
    NatTy ->
      -- Generate nat possibilities
      let gamma' = if isAdditive then [] else gamma in
      case howManyNatPossibilities ?configuration of
        1 -> lift [(Ext Zero, gamma', [])]
        _ -> lift [(Ext Zero, gamma', []), (App (Ext Succ) (Ext Zero), gamma', [])]
    _     -> none


pairElimHelper :: (?configuration :: Configuration)
  => Context -> Context -> Context -> Bool -> Type -> StateT Int [] (Expr PCF, Context, Substitution)
pairElimHelper left [] _ _ _ = none
pairElimHelper left (var@(x, a):right) gamma False goalTy =
  (pairElimHelper (var:left) right gamma False goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega False in
    case (canUse, t) of
      (True, ProdTy t1 t2) -> do
          l <- freshVar "x"
          r <- freshVar "x"
          let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
          let (gamma'', omega''') = bindToContext (r, Linear t2) gamma' omega'' (isLAsync t2)
          (e, delta, subst) <- synthesise True False gamma'' omega''' goalTy
          case (lookup l delta, lookup r delta) of
            (Nothing, Nothing) -> return ((Ext (LetP l r (Var x) e)), delta, subst)
            _ -> none
      _ -> none

pairElimHelper left (var@(x, a):right) gamma True goalTy =
  (pairElimHelper (var:left) right gamma True goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega True in
    case (canUse, t) of
      (True, ProdTy t1 t2) -> do
          l <- freshVar "x"
          r <- freshVar "x"
          let omega1 = computeAddInputCtx omega omega'
          let (gamma', omega1') = bindToContext (l, Linear t1) gamma omega1 (isLAsync t1)
          let (gamma'', omega1'') = bindToContext (r, Linear t2) gamma' omega1' (isLAsync t2)
          (e, delta, subst) <- synthesise True True gamma'' omega1'' goalTy
          let delta' = computeAddOutputCtx omega' delta []
          case lookupAndCutout l delta' of
            Just (delta', Linear _) ->
              case lookupAndCutout r delta' of
                Just (delta''', Linear _) -> return ((Ext (LetP l r (Var x) e)), delta''', subst)
                _ -> none
            _ -> none
      _ -> none

pairIntroHelper :: (?configuration :: Configuration)
  => Context -> Bool -> Type -> StateT Int [] (Expr PCF, Context, Substitution)
pairIntroHelper gamma False goalTy =
  case goalTy of
    ProdTy t1 t2 -> do
      (e1, delta1, subst1) <- synthesise True False gamma [] t1
      (e2, delta2, subst2) <- synthesise True False delta1 [] t2
      let subst = combineSubstitutions subst1 subst2
      case subst of
        Just subst' -> return ((Ext (Pair e1 e2)), delta2, subst')
        Nothing -> none
    _ -> none

pairIntroHelper gamma True goalTy =
  case goalTy of
    ProdTy t1 t2 -> do
      (e1, delta1, subst1) <- synthesise True True gamma [] t1
      let gamma2 = computeAddInputCtx gamma delta1
      (e2, delta2, subst2) <- synthesise True True gamma2 [] t2
      let delta3 = computeAddOutputCtx delta1 delta2 []
      let subst = combineSubstitutions subst1 subst2
      case subst of
        Just subst' -> return ((Ext (Pair e1 e2)), delta3, subst')
        Nothing -> none
    _ -> none


sumIntroHelper :: (?configuration :: Configuration)
  => Context -> Bool -> Type -> StateT Int [] (Expr PCF, Context, Substitution)
sumIntroHelper gamma isAdditive goalTy =
  case goalTy of
    SumTy t1 t2 -> do
      try
        (do { (e1, delta1, subst1) <- synthesise True isAdditive gamma [] t1; return (Ext (Inl (e1)), delta1, subst1) })
        (do { (e2, delta2, subst2) <- synthesise True isAdditive gamma [] t2; return (Ext (Inr (e2)), delta2, subst2) })
    _ -> none


sumElimHelper :: (?configuration :: Configuration)
  => Context -> Context -> Context -> Bool -> Type -> StateT Int [] (Expr PCF, Context, Substitution)
sumElimHelper left [] _ _ _ = none
sumElimHelper left (var@(x, a):right) gamma False goalTy =
  (sumElimHelper (var:left) right gamma False goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega False in
    case (canUse, t) of
      (True, SumTy t1 t2) -> do
        l <- freshVar "x"
        r <- freshVar "x"
        let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
        let (gamma'', omega''') = bindToContext (r, Linear t2) gamma' omega'' (isLAsync t2)
        (e1, delta1, subst1) <- synthesise True False gamma' omega'' goalTy
        (e2, delta2, subst2) <- synthesise True False gamma'' omega''' goalTy
        let subst = combineSubstitutions subst1 subst2
        case subst of
          Just subst' ->
            case (lookup l delta1, lookup r delta2) of
              (Nothing, Nothing) ->
                case ctxGlb delta1 delta2 of
                  Just delta3 ->
                    return (Ext (Case (Var x) (l, e1) (r, e2)), delta3, subst')
                  Nothing -> none
              _ -> none
          _ -> none
      _ -> none

sumElimHelper left (var@(x, a):right) gamma True goalTy =
  (sumElimHelper (var:left) right gamma True goalTy) `try`
  let omega = left ++ right in
  let (canUse, omega', t) = useVar var omega True in
    case (canUse, t) of
      (True, SumTy t1 t2) -> do
        l <- freshVar "x"
        r <- freshVar "x"
        let omega1 = computeAddInputCtx omega omega'
        let (gamma', omega1') = bindToContext (l, Linear t1) gamma omega1 (isLAsync t1)
        let (gamma'', omega1'') = bindToContext (r, Linear t2) gamma' omega1' (isLAsync t2)
        (e1, delta1, subst1) <- synthesise True True gamma' omega1' goalTy
        (e2, delta2, subst2) <- synthesise True True gamma'' omega1'' goalTy
        let subst = combineSubstitutions subst1 subst2
        case subst of
          Just subst' ->
            case (lookupAndCutout l delta1, lookupAndCutout r delta2) of
              (Just (delta1', Linear _), Just (delta2', Linear _)) ->
                case ctxLub delta1' delta2' of
                  Just delta3 ->
                    let delta3' = computeAddOutputCtx omega' delta3 [] in do
                      traceM $ show delta3'
                      return (Ext (Case (Var x) (l, e1) (r, e2)), delta3', subst')
                  Nothing -> do
                    none
              _ -> do
                none
          _ -> none
      _ -> none
-}

synthesise :: (?globals :: Globals)
           => Bool           -- whether a function is allowed at this point
           -> Bool           -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption)        -- free variables
           -> Ctxt (Assumption)        -- focused variables
           -> Type           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption), Substitution)

synthesise allowLam isAdd gamma omega goalTy =
  (varHelper [] gamma isAdd goalTy) `try` (absHelper gamma omega allowLam isAdd goalTy) `try` (appHelper gamma omega isAdd goalTy)
