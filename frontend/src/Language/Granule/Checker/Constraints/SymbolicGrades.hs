{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DataKinds #-}

-- | Provides a symbolic representation of grades (coeffects, effects, indices)
-- in order for a solver to use.
module Language.Granule.Checker.Constraints.SymbolicGrades where

import Language.Granule.Checker.Constraints.SNatX
import Language.Granule.Syntax.Type

import Data.Functor.Identity
import Control.Monad.IO.Class
import Control.Monad (liftM2)
-- import System.Exit (die)
import Control.Exception

import qualified Data.Text as T
import GHC.Generics (Generic)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.SBV.Set as S

solverError :: MonadIO m => String -> m a
solverError msg = liftIO $ throwIO . ErrorCall $ msg

-- Symbolic grades, for coeffects and indices
data SGrade =
       SNat      SInteger
     | SFloat    SFloat
     | SLevel    SInteger
     | SSec      SBool -- Hi = True, Lo = False
     | SSet      Polarity (SSet SSetElem)
     | SExtNat   { sExtNat :: SNatX }
     | SInterval { sLowerBound :: SGrade, sUpperBound :: SGrade }
     -- Single point coeffect (not exposed at the moment)
     | SPoint
     | SProduct { sfst :: SGrade, ssnd :: SGrade }
     -- | Coeffect with 1 + 1 = 0. False is 0, True is 1.
     -- |
     -- | Grade '0' denotes even usage, and grade '1' denotes odd usage.
     | SOOZ SBool
     -- LNL
     | SLNL SBool -- True = NonLin, False = Lin

     -- A kind of embedded uninterpreted sort which can accept some equations
     -- Used for doing some limited solving over poly coeffect grades
     | SUnknown SynTree

    deriving (Show, Generic)

-- Symbolic elements (TODO: generalise in the future as needed)
-- For now only strings can be set elements
type SSetElem = [Char]

-- Specialised representation for `Level`
publicRepresentation, privateRepresentation, unusedRepresentation, dunnoRepresentation :: Integer
privateRepresentation = 1
publicRepresentation  = 2
unusedRepresentation  = 0
dunnoRepresentation   = 3

-- Representation for `Sec`
hiRepresentation, loRepresentation :: SBool
hiRepresentation = sTrue
loRepresentation = sFalse

-- Representation of semiring terms as a `SynTree`
data SynTree =
    SynPlus SynTree SynTree
  | SynTimes SynTree SynTree
  | SynMeet SynTree SynTree
  | SynJoin SynTree SynTree
  | SynLeaf (Maybe SInteger)  -- Just 0 and Just 1 can be identified
  | SynMerge SBool SynTree SynTree

instance Show SynTree where
  show (SynPlus s t) = "(" ++ show s ++ " + " ++ show t ++ ")"
  show (SynTimes s t) = show s ++ " * " ++ show t
  show (SynJoin s t) = "(" ++ show s ++ " \\/ " ++ show t ++ ")"
  show (SynMeet s t) = "(" ++ show s ++ " /\\ " ++ show t ++ ")"
  show (SynLeaf Nothing) = "?"
  show (SynLeaf (Just n)) = T.unpack $
    T.replace (T.pack $ " :: SInteger") (T.pack "") (T.pack $ show n)
  show (SynMerge sb s t) = "(if " ++ show sb ++ " (" ++ show s ++ ") (" ++ show t ++ "))"

sEqTree :: SynTree -> SynTree -> Symbolic SBool

sEqTree (SynPlus s s') (SynPlus t t') =
  liftM2 (.||) (liftM2 (.&&) (sEqTree s t) (sEqTree s' t'))
                -- + is commutative
               (liftM2 (.&&) (sEqTree s' t) (sEqTree s t'))

sEqTree (SynTimes s s') (SynTimes t t') = liftM2 (.&&) (sEqTree s t) (sEqTree s' t')
sEqTree (SynMeet s s') (SynMeet t t')   =
  liftM2 (.||) (liftM2 (.&&) (sEqTree s t) (sEqTree s' t'))
               -- /\ is commutative
               (liftM2 (.&&) (sEqTree s t') (sEqTree s' t))
sEqTree (SynJoin s s') (SynJoin t t')   =
  liftM2 (.||) (liftM2 (.&&) (sEqTree s t) (sEqTree s' t'))
              -- \/ is commutative
              (liftM2 (.&&) (sEqTree s t') (sEqTree s' t))

sEqTree (SynMerge sb s s') (SynMerge sb' t t')  =
  liftM2 (.||)
    (liftM2 (.&&) (liftM2 (.&&) (sEqTree s t) (sEqTree s' t'))
                  (return $ sb .== sb'))
    -- Flipped branching
    (liftM2 (.&&) (liftM2 (.&&) (sEqTree s t') (sEqTree s t))
                  (return $ sb .== sNot sb'))


sEqTree (SynLeaf Nothing) (SynLeaf Nothing) = return $ sFalse
sEqTree (SynLeaf (Just n)) (SynLeaf (Just n')) = return $ n .=== n'
sEqTree s t = return sFalse

sLtTree :: SynTree -> SynTree -> Symbolic SBool
sLtTree (SynPlus s s') (SynPlus t t')   = liftM2 (.&&) (sLtTree s t) (sLtTree s' t')
sLtTree (SynTimes s s') (SynTimes t t') = liftM2 (.&&) (sLtTree s t) (sLtTree s' t')
sLtTree (SynMeet s s') (SynMeet t t')   = liftM2 (.&&) (sLtTree s t) (sLtTree s' t')
sLtTree (SynJoin s s') (SynJoin t t')   = liftM2 (.&&) (sLtTree s t) (sLtTree s' t')
sLtTree (SynMerge sb s s') (SynMerge sb' t t') =
  liftM2 (.&&) (return $ sb .== sb') (liftM2 (.&&) (sLtTree s t) (sLtTree s' t'))
sLtTree (SynLeaf Nothing) (SynLeaf Nothing) = return $ sFalse
sLtTree (SynLeaf (Just n)) (SynLeaf (Just n')) = return $ n .< n'
sLtTree _ _ = return $ sFalse

---- SGrade operations

-- Work out if two symbolic grades are of the same type
match :: SGrade -> SGrade -> Bool
match (SNat _) (SNat _) = True
match (SFloat _) (SFloat _) = True
match (SLevel _) (SLevel _) = True
match (SSet p _) (SSet p' _) | p == p' = True
match (SExtNat _) (SExtNat _) = True
match (SInterval s1 s2) (SInterval t1 t2) = match s1 t1 && match s2 t2
match SPoint SPoint = True
match (SProduct s1 s2) (SProduct t1 t2) = match s1 t1 && match s2 t2
match (SUnknown _) (SUnknown _) = True
match (SOOZ _) (SOOZ _) = True
match (SSec _) (SSec _) = True
match (SLNL _) (SLNL _) = True
match _ _ = False

isSProduct :: SGrade -> Bool
isSProduct (SProduct _ _) = True
isSProduct _ = False

applyToProducts :: Monad m => (SGrade -> SGrade -> m a)
            -> (a -> a -> b)
            -> (SGrade -> a)
            -> SGrade -> SGrade -> Either String (m b)

applyToProducts f g _ a@(SProduct a1 b1) b@(SProduct a2 b2) =
  if (match a1 a2) && (match b1 b2)
    then Right $ liftM2 g (f a1 a2) (f b1 b2)
    else if (match a1 b2) && (match b1 a2)
      then Right $ liftM2 g (f a1 b2) (f b1 a2)
      else Left $ "Solver grades " <> show a <> " and " <> show b <> " are incompatible "

applyToProducts f g h a@(SProduct a1 b1) c =
  if match a1 c
    then Right $ liftM2 g (f a1 c) (return $ h b1)
    else if match b1 c
         then Right $ liftM2 g (return $ h a1) (f b1 c)
         else Left $ "Solver grades " <> show a <> " and " <> show c <> " are incompatible "

applyToProducts f g h c a@(SProduct a1 b1) =
  if match c a1
    then Right $ liftM2 g (f c a1) (return $ h b1)
    else if match c b1
         then Right $ liftM2 g (return $ h a1) (f c b1)
         else Left $ "Solver grades " <> show a <> " and " <> show c <> " are incompatible "

applyToProducts _ _ _ a b =
  Left $ "Solver grades " <> show a <> " and " <> show b <> " are not products"

natLike :: SGrade -> Bool
natLike (SNat _) = True
natLike (SExtNat _) = True
natLike _ = False

instance Mergeable SGrade where
  symbolicMerge s sb (SNat n) (SNat n') = SNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SFloat n) (SFloat n') = SFloat (symbolicMerge s sb n n')
  symbolicMerge s sb (SLevel n) (SLevel n') = SLevel (symbolicMerge s sb n n')
  symbolicMerge s sb (SSet _ n) (SSet _ n') = error "Can't symbolic merge sets yet"
  symbolicMerge s sb (SExtNat n) (SExtNat n') = SExtNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (symbolicMerge s sb lb1 lb2) (symbolicMerge s sb ub1 ub2)
  symbolicMerge s sb SPoint SPoint = SPoint

  symbolicMerge s sb a b | isSProduct a || isSProduct b =
    either error runIdentity (applyToProducts (\a b -> return $ symbolicMerge s sb a b) SProduct id a b)

  symbolicMerge s sb (SUnknown (SynLeaf (Just u))) (SUnknown (SynLeaf (Just u'))) =
    SUnknown (SynLeaf (Just (symbolicMerge s sb u u')))

  symbolicMerge s sb (SUnknown a) (SUnknown b) = SUnknown (SynMerge sb a b)
  symbolicMerge s sb (SSec a) (SSec b) = SSec (symbolicMerge s sb a b)
  symbolicMerge s sb (SLNL a) (SLNL b) = SLNL (symbolicMerge s sb a b)

  symbolicMerge _ _ s t = error $ cannotDo "symbolicMerge" s t

symGradeLess :: SGrade -> SGrade -> Symbolic SBool
symGradeLess (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (symGradeLess lb2 lb1) (symGradeLess ub1 ub2)

symGradeLess (SNat n) (SNat n')     = return $ n .< n'
symGradeLess (SFloat n) (SFloat n') = return $ n .< n'
symGradeLess (SLevel n) (SLevel n') = -- return $ n .< n'
  return $ ite ((n .== literal dunnoRepresentation) .&& (n' .== literal publicRepresentation)) sTrue
         $ ite ((n .== literal dunnoRepresentation) .|| (n' .== literal dunnoRepresentation)) sFalse
         $ n .< n'
symGradeLess (SSet _ n) (SSet _ n')  = solverError "Can't do < on sets"
symGradeLess (SExtNat n) (SExtNat n') = return $ n .< n'
symGradeLess SPoint SPoint            = return sTrue
symGradeLess (SUnknown s) (SUnknown t) = sLtTree s t

symGradeLess s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradeLess (.&&) (const sTrue) s t)

symGradeLess s t = solverError $ cannotDo ".<" s t

symGradeGreater :: SGrade -> SGrade -> Symbolic SBool
symGradeGreater x y = symGradeLess y x

symGradeLessEq :: SGrade -> SGrade -> Symbolic SBool
symGradeLessEq x y = lazyOrSymbolicM (symGradeEq x y) (symGradeLess x y)

symGradeGreaterEq :: SGrade -> SGrade -> Symbolic SBool
symGradeGreaterEq x y = lazyOrSymbolicM (symGradeEq x y) (symGradeGreater x y)

-- A short-circuiting disjunction for effectful computations that
-- produce symoblic bools (a kind of expanded `iteLazy` for Symbolic monad)
lazyOrSymbolicM :: Symbolic SBool -> Symbolic SBool -> Symbolic SBool
lazyOrSymbolicM m1 m2 = m1 >>= \b1 ->
  case unliteral b1 of
    Just True -> return sTrue
    otherwise -> m2 >>= \b2 -> return $ symbolicMerge False b1 sTrue b2

symGradeEq :: SGrade -> SGrade -> Symbolic SBool
symGradeEq (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (symGradeEq lb2 lb1) (symGradeEq ub1 ub2)

symGradeEq (SNat n) (SNat n')     = return $ n .== n'
symGradeEq (SFloat n) (SFloat n') = return $ n .== n'
symGradeEq (SLevel n) (SLevel n') = return $ n .== n'
symGradeEq (SSet p n) (SSet p' n') | p == p' = return $ n .== n'
symGradeEq (SExtNat n) (SExtNat n') = return $ n .== n'
symGradeEq SPoint SPoint          = return $ sTrue
symGradeEq (SOOZ s) (SOOZ r)      = pure $ s .== r
symGradeEq s t | isSProduct s || isSProduct t =
    either solverError id (applyToProducts symGradeEq (.&&) (const sTrue) s t)

symGradeEq (SUnknown t) (SUnknown t') = sEqTree t t'
symGradeEq (SSec n) (SSec n') = return $ n .== n'
symGradeEq (SLNL n) (SLNL m) = return $ n .== m
symGradeEq s t = solverError $ cannotDo ".==" s t

-- | Meet operation on symbolic grades
symGradeMeet :: SGrade -> SGrade -> Symbolic SGrade
symGradeMeet (SNat n1) (SNat n2)     = return $ SNat $ n1 `smin` n2
symGradeMeet (SSet Normal s) (SSet Normal t) = return $ SSet Normal $ S.union s t
symGradeMeet (SSet Opposite s) (SSet Opposite t) = return $ SSet Opposite $ S.intersection s t
symGradeMeet (SLevel s) (SLevel t)   = return $ SLevel $ s `smin` t
symGradeMeet (SFloat n1) (SFloat n2) = return $ SFloat $ n1 `smin` n2
symGradeMeet (SExtNat x) (SExtNat y) = return $ SExtNat $
  ite (isInf x) y (ite (isInf y) x (SNatX (xVal x `smin` xVal y)))
symGradeMeet (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 SInterval (lb1 `symGradeJoin` lb2) (ub1 `symGradeMeet` ub2)
symGradeMeet SPoint SPoint = return SPoint
symGradeMeet s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradeMeet SProduct id s t)

symGradeMeet (SUnknown (SynLeaf (Just n))) (SUnknown (SynLeaf (Just n'))) =
  return $ SUnknown (SynLeaf (Just (n `smin` n')))
symGradeMeet (SUnknown t) (SUnknown t') = return $ SUnknown (SynMeet t t')
symGradeMeet (SSec a) (SSec b) = return $ SSec (a .&& b)
symGradeMeet s t = solverError $ cannotDo "meet" s t

-- | Join operation on symbolic grades
symGradeJoin :: SGrade -> SGrade -> Symbolic SGrade
symGradeJoin (SNat n1) (SNat n2) = return $ SNat (n1 `smax` n2)
symGradeJoin (SSet Normal s) (SSet Normal t)   = return $ SSet Normal $ S.intersection s t
symGradeJoin (SSet Opposite s) (SSet Opposite t) = return $ SSet Opposite $ S.union s t
symGradeJoin (SLevel s) (SLevel t) =
  return $ SLevel $ ite (s .== literal unusedRepresentation) t -- 0 + t = t
                  $ ite (t .== literal unusedRepresentation) s -- s + 0 = s
                  $ ite (s .== literal dunnoRepresentation)  t
                  $ ite (t .== literal dunnoRepresentation)  s
                  $ s `smax` t
symGradeJoin (SFloat n1) (SFloat n2) = return $ SFloat (n1 `smax` n2)
symGradeJoin (SExtNat x) (SExtNat y) = return $ SExtNat $
  ite (isInf x .|| isInf y) inf (SNatX (xVal x `smax` xVal y))
symGradeJoin (SInterval lb1 ub1) (SInterval lb2 ub2) =
   liftM2 SInterval (lb1 `symGradeMeet` lb2) (ub1 `symGradeJoin` ub2)
symGradeJoin SPoint SPoint = return SPoint
symGradeJoin s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradeJoin SProduct id s t)

symGradeJoin (SUnknown (SynLeaf (Just n))) (SUnknown (SynLeaf (Just n'))) =
  return $ SUnknown (SynLeaf (Just (n `smax` n')))
symGradeJoin (SUnknown t) (SUnknown t') = return $ SUnknown (SynJoin t t')
symGradeJoin (SSec a) (SSec b) = return $ SSec (a .|| b)
symGradeJoin s t = solverError $ cannotDo "join" s t

-- | Plus operation on symbolic grades
symGradePlus :: SGrade -> SGrade -> Symbolic SGrade
symGradePlus (SNat n1) (SNat n2) = return $ SNat (n1 + n2)
symGradePlus (SSet Normal s) (SSet Normal t) = return $ SSet Normal $ S.union s t
symGradePlus (SSet Opposite s) (SSet Opposite t) = return $ SSet Opposite $ S.intersection s t
symGradePlus (SLevel lev1) (SLevel lev2) =
  return $ SLevel $ ite (lev1 .== literal unusedRepresentation) lev2
                  $ ite (lev2 .== literal unusedRepresentation) lev1
                  $ ite ((lev1 .== literal dunnoRepresentation)
                         .&& (lev2 .== literal privateRepresentation)) (literal dunnoRepresentation)
                  $ ite ((lev2 .== literal dunnoRepresentation)
                         .&& (lev1 .== literal privateRepresentation)) (literal dunnoRepresentation)
                  $ ite (lev1 .== literal dunnoRepresentation) lev2
                  $ ite (lev2 .== literal dunnoRepresentation) lev1
                  $ lev1 `smax` lev2
symGradePlus (SFloat n1) (SFloat n2) = return $ SFloat $ n1 + n2
symGradePlus (SExtNat x) (SExtNat y) = return $ SExtNat (x + y)
symGradePlus (SInterval lb1 ub1) (SInterval lb2 ub2) =
    liftM2 SInterval (lb1 `symGradePlus` lb2) (ub1 `symGradePlus` ub2)
symGradePlus SPoint SPoint = return $ SPoint
symGradePlus s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradePlus SProduct id s t)
-- 1 + 1 = 0
symGradePlus (SOOZ s) (SOOZ r) = pure . SOOZ $ ite s (sNot r) r

-- Direct encoding of additive unit
symGradePlus (SUnknown t@(SynLeaf (Just u))) (SUnknown t'@(SynLeaf (Just u'))) =
  return $ ite (u .== 0) (SUnknown (SynLeaf (Just u')))
    (ite (u' .== 0) (SUnknown (SynLeaf (Just u))) (SUnknown (SynPlus t t')))

symGradePlus (SUnknown t@(SynLeaf (Just u))) (SUnknown t') =
  return $ ite (u .== 0) (SUnknown t') (SUnknown (SynPlus t t'))

symGradePlus (SUnknown t) (SUnknown t'@(SynLeaf (Just u))) =
  return $ ite (u .== 0) (SUnknown t) (SUnknown (SynPlus t t'))

symGradePlus (SUnknown um) (SUnknown un) =
  return $ SUnknown (SynPlus um un)

symGradePlus (SSec a) (SSec b) = symGradeMeet (SSec a) (SSec b)
symGradePlus (SLNL a) (SLNL b) = return $ SLNL sTrue

symGradePlus s t = solverError $ cannotDo "plus" s t

-- | Converge (#) operation
symGradeConverge :: SGrade -> SGrade -> Symbolic SGrade
symGradeConverge (SLevel lev1) (SLevel lev2) = do
    v <- symGradeTimes (SLevel lev1) (SLevel lev2)
    return $ ite (lev1 .== literal privateRepresentation)
                 (SLevel $ literal privateRepresentation)
                 $ ite (lev2 .== literal privateRepresentation)
                       (SLevel $ literal privateRepresentation)
                       v
symGradeConverge s1 s2 = symGradeTimes s1 s2

-- | Times operation on symbolic grades
symGradeTimes :: SGrade -> SGrade -> Symbolic SGrade
symGradeTimes (SNat n1) (SNat n2) = return $ SNat (n1 * n2)
symGradeTimes (SNat n1) (SExtNat (SNatX n2)) = return $ SExtNat $ SNatX (n1 * n2)
symGradeTimes (SExtNat (SNatX n1)) (SNat n2) = return $ SExtNat $ SNatX (n1 * n2)
symGradeTimes (SSet Normal s) (SSet Normal t) = return $ SSet Normal $ S.intersection s t
symGradeTimes (SSet Opposite s) (SSet Opposite t) = return $ SSet Opposite $ S.union s t
symGradeTimes (SLevel lev1) (SLevel lev2) =
  return $ SLevel $ ite (lev1 .== literal unusedRepresentation)  (literal unusedRepresentation) -- 0 * r = 0
                  $ ite (lev2 .== literal unusedRepresentation)  (literal unusedRepresentation) -- r * 0 = 0
                  $ ite (lev1 .== literal privateRepresentation) lev2 -- 1 * r = r
                  $ ite (lev2 .== literal privateRepresentation) lev1 -- r * 1 = r
                  $ ite (lev1 .== literal dunnoRepresentation)   lev2
                  $ ite (lev2 .== literal dunnoRepresentation)   lev1
                  $ lev1 `smax` lev2
symGradeTimes (SFloat n1) (SFloat n2) = return $ SFloat $ n1 * n2
symGradeTimes (SExtNat x) (SExtNat y) = return $ SExtNat (x * y)
symGradeTimes (SOOZ s) (SOOZ r) = pure . SOOZ $ s .&& r

symGradeTimes (SInterval lb1 ub1) (SInterval lb2 ub2) =
    liftM2 SInterval (comb symGradeMeet) (comb symGradeJoin)
     where
      comb f = do
        lb1lb2 <- lb1 `symGradeTimes` lb2
        lb1ub2 <- lb1 `symGradeTimes` ub2
        ub1lb2 <- ub1 `symGradeTimes` lb2
        ub1ub2 <- ub1 `symGradeTimes` ub2
        a <- lb1lb2 `f` lb1ub2
        b <- a `f` ub1lb2
        b `f` ub1ub2

symGradeTimes SPoint SPoint = return SPoint
symGradeTimes s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradeTimes SProduct id s t)

-- units and absorption directly encoded
symGradeTimes (SUnknown t@(SynLeaf (Just u))) (SUnknown t'@(SynLeaf (Just u'))) =
  return $
     ite (u .== 1) (SUnknown (SynLeaf (Just u')))
       (ite (u' .== 1) (SUnknown (SynLeaf (Just u)))
         (ite (u .== 0) (SUnknown (SynLeaf (Just 0)))
           (ite (u' .== 0) (SUnknown (SynLeaf (Just 0)))
              (SUnknown (SynTimes t t')))))

symGradeTimes (SUnknown t@(SynLeaf (Just u))) (SUnknown t') =
  return $
    ite (u .== 1) (SUnknown t')
      (ite (u .== 0) (SUnknown (SynLeaf (Just 0))) (SUnknown (SynTimes t t')))

symGradeTimes (SUnknown t) (SUnknown t'@(SynLeaf (Just u))) =
   return $
     ite (u .== 1) (SUnknown t)
       (ite (u .== 0) (SUnknown (SynLeaf (Just 0))) (SUnknown (SynTimes t t')))

symGradeTimes (SUnknown um) (SUnknown un) =
  return $ SUnknown (SynTimes um un)

symGradeTimes (SSec a) (SSec b) = symGradeJoin (SSec a) (SSec b)
symGradeTimes (SLNL a) (SLNL b) = return $ SLNL $ a .&& b

symGradeTimes s t = solverError $ cannotDo "times" s t

-- | Minus operation on symbolic grades (if the user writes -)
-- | (OPTIONAL)
symGradeMinus :: SGrade -> SGrade -> Symbolic SGrade
symGradeMinus (SNat n1) (SNat n2) = return $ SNat $ ite (n1 .< n2) 0 (n1 - n2)
symGradeMinus (SSet p s) (SSet p' t) | p == p' = return $ SSet p (s S.\\ t)
symGradeMinus (SExtNat x) (SExtNat y) = return $ SExtNat (x - y)
symGradeMinus (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 SInterval (lb1 `symGradeMinus` lb2) (ub1 `symGradeMinus` ub2)
symGradeMinus SPoint SPoint = return $ SPoint
symGradeMinus s t | isSProduct s || isSProduct t =
  either solverError id (applyToProducts symGradeMinus SProduct id s t)
symGradeMinus s t = solverError $ cannotDo "minus" s t

cannotDo :: String -> SGrade -> SGrade -> String
cannotDo op (SUnknown s) (SUnknown t) =
  "It is unknown whether "
      <> show s <> " "
      <> op <> " "
      <> show t
      <> " holds for all resource algebras."

cannotDo op s t =
  "Cannot perform symbolic operation `"
      <> op <> "` on "
      <> show s <> " and "
      <> show t
