{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Syntax of types, coeffects, and effects

module Language.Granule.Syntax.Type where

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

import Data.Functor.Identity (runIdentity)
import GHC.Generics (Generic)
import Data.Data
import Data.Functor.Const
-- Distinguish Haskell's Type kind from the representation of Granule types
import qualified Data.Kind as Haskell (Type)
import Unsafe.Coerce -- because GHC does not have dependent types

-- | Represent types with a universal quantification at the start
data TypeScheme =
  Forall
    Span          -- span of the scheme
    [(Id, Kind)]  -- binders
    [Type Zero]      -- constraints
    (Type Zero)      -- type
  deriving (Eq, Show, Generic, Data)

-- Constructors and operators are just strings
data TypeOperator
  = TyOpLesser
  | TyOpLesserEq
  | TyOpGreater
  | TyOpGreaterEq
  | TyOpEq
  | TyOpNotEq
  | TyOpPlus
  | TyOpTimes
  | TyOpMinus
  | TyOpExpon
  | TyOpMeet
  | TyOpJoin
  deriving (Eq, Ord, Show, Typeable, Data)


type One = Succ Zero
type Two = Succ One

type Kind = Type One

data Nat = Succ Nat | Zero
 deriving Eq

data ULevel (l :: Nat) where
  LSucc :: ULevel l -> ULevel (Succ l)
  LZero :: ULevel Zero

data IsLevel where
  IsLevel :: ULevel l -> IsLevel

deriving instance Show IsLevel

class LesserLevel (l :: Nat) (l' :: Nat) where
instance LesserLevel Zero (Succ l) where
-- instance LesserLevel l l' => LesserLevel (Succ l) (Succ l')

deriving instance Eq (ULevel l)
deriving instance Show (ULevel l)
deriving instance Ord (ULevel l)

--tyPromote :: LesserLevel l l' => Type l -> Maybe (Type l')
tyPromote :: Type l -> Maybe (Type (Succ l))
tyPromote (Type l) = return $ Type (LSucc l)
tyPromote (FunTy v t1 t2) = do
  t1 <- tyPromote t1
  t2 <- tyPromote t2
  return $ FunTy v t1 t2
tyPromote (TyCon i) = return $ TyCon i
tyPromote (TyVar i) = return $ TyVar i
tyPromote (TyApp t1 t2) = do
  t1 <- tyPromote t1
  t2 <- tyPromote t2
  return $ TyApp t1 t2
tyPromote (TyInt n) = return $ TyInt n
tyPromote (TyInfix op t1 t2) = do
  t1 <- tyPromote t1
  t2 <- tyPromote t2
  return $ TyInfix op t1 t2
tyPromote (TySet ts) = do
  ts <- mapM tyPromote ts
  return $ TySet ts
tyPromote (TyCase t ts) = do
  t <- tyPromote t
  ts <- mapM (\(a,b) -> extractMonad (tyPromote a, tyPromote b)) ts
  return $ TyCase t ts
    where
      extractMonad (a,b) = do
        a' <- a
        b' <- b
        return (a', b')
tyPromote t = Nothing

data TypeWithLevel where
  TypeWithLevel :: ULevel l -> Type l -> TypeWithLevel

deriving instance Show TypeWithLevel

-- This is only used for testing and should really be avoided
-- elsewhere
instance Eq TypeWithLevel where
  (TypeWithLevel u t) == (TypeWithLevel u' t') =
    (show u == show u') && (show t == show t')

{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}

data Type (l :: Nat) where
    Type    :: ULevel l -> Type (Succ l)        -- ^ Universe construction
    FunTy   :: Maybe Id -> Type l  -> Type l -> Type l  -- ^ Function type

    TyCon   :: Id -> Type l                 -- ^ Type constructor
    Box     :: Coeffect -> Type Zero -> Type Zero -- ^ Coeffect type
    Diamond :: Type Zero -> Type Zero -> Type Zero   -- ^ Effect type
    TyVar   :: Id -> Type l                 -- ^ Type variable
    TyApp   :: Type l -> Type l -> Type l   -- ^ Type application
    TyInt   :: Int -> Type l                -- ^ Type-level Int
    TyInfix :: TypeOperator -> Type l -> Type l -> Type l -- ^ Infix type operator
    TySet   :: [Type l] -> Type l           -- ^ Type-level set
    TyCase  :: Type l -> [(Type l, Type l)] -> Type l -- ^ Type-level case
    KUnion  :: Type (Succ (Succ Zero)) -> Type (Succ (Succ Zero)) -> Type (Succ (Succ Zero))
    TySig   :: Type l -> Type (Succ l) -> Type l

deriving instance Show (Type l)
deriving instance Eq (Type l)
deriving instance Ord (Type l)
deriving instance Typeable (Type l)

instance Typeable l => Data (Type l) where
  gunfold    = gunfold
  toConstr   = error "Internal bug: Cannot use a Data instance on `Type l` yet"
  dataTypeOf = error "Internal bug: Cannot use a Data instance on `Type l` yet"

data LevelProxy (l :: Nat) = LevelProxy

getLevel :: forall l . HasLevel l => Type l -> ULevel l
getLevel _ = getLevel' (LevelProxy :: LevelProxy l)

class HasLevel (l :: Nat) where
  getLevel' :: LevelProxy l -> ULevel l

instance HasLevel Zero where
  getLevel' LevelProxy = LZero

instance HasLevel l => HasLevel (Succ l) where
  getLevel' LevelProxy = LSucc (getLevel' (LevelProxy :: LevelProxy l))

getUntypedLevel :: ULevel l -> Nat
getUntypedLevel LZero = Zero
getUntypedLevel (LSucc l) = Succ (getUntypedLevel l)

isAtLevel :: ULevel l' -> Type l' -> ULevel l -> Maybe (Type l)
isAtLevel l t l' =
  if getUntypedLevel l == getUntypedLevel l'
    then Just (unsafeCoerce t)
    else Nothing

{-
promoteTypeToKind :: Type -> Kind
promoteTypeToKind (TyVar v) = KVar v
promoteTypeToKind t = TyPromote t

demoteKindToType :: Kind -> Maybe Type
demoteKindToType (TyPromote t) = Just t
demoteKindToType (KVar v)     = Just (TyVar v)
demoteKindToType _            = Nothing

instance Term Kind where
  freeVars (TyPromote t) = freeVars t
  freeVars (KVar x)     = [x]
  freeVars _            = []

  isLexicallyAtomic KVar{} = True
  isLexicallyAtomic KType{} = True
  isLexicallyAtomic KCoeffect{} = True
  isLexicallyAtomic KEffect{} = True
  isLexicallyAtomic KPredicate{} = True
  isLexicallyAtomic TyPromote{} = True
  isLexicallyAtomic _ = False
-}

-- Smart constructors

funTy :: Type l -> Type l -> Type l
funTy = FunTy Nothing

tyCon :: String -> Type l
tyCon = TyCon . mkId

kNat, protocol :: Kind
kNat = TyCon $ mkId "Nat"
protocol = TyCon $ mkId "Protocol"

{-
instance Monad m => Freshenable m Kind where
  freshen KType = return KType
  freshen KCoeffect = return KCoeffect
  freshen KEffect = return KEffect
  freshen KPredicate = return KPredicate
  freshen (KFun k1 k2) = do
    k1 <- freshen k1
    k2 <- freshen k2
    return $ KFun k1 k2

  freshen (KVar v) = do
    v' <- lookupVar  TypeL v
    case v' of
       Just v' -> return (KVar $ Id (sourceName v) v')
       -- This case happens if we are referring to a defined
       -- function which does not get its name freshened
       Nothing -> return (KVar $ mkId (sourceName v))

  freshen (TyPromote ty) = do
     ty <- freshen ty
     return $ TyPromote ty

  freshen (KUnion k1 k2) = do
    k1' <- freshen k1
    k2' <- freshen k2
    return $ KUnion k1' k2'
    -}

-- | Represents coeffect grades
data Coeffect = CNat      Int
              | CFloat    Rational
              | CInfinity (Maybe (Type One))
              | CInterval { lowerBound :: Coeffect, upperBound :: Coeffect }
              | CVar      Id
              | CPlus     Coeffect Coeffect
              | CTimes    Coeffect Coeffect
              | CMinus    Coeffect Coeffect
              | CMeet     Coeffect Coeffect
              | CJoin     Coeffect Coeffect
              | CZero     (Type One)
              | COne      (Type One)
              | Level     Integer
              | CSet      [(String, Type Zero)]
              | CSig      Coeffect (Type One)
              | CExpon    Coeffect Coeffect
              | CProduct  Coeffect Coeffect
    deriving (Eq, Ord, Show)

-- Algebra for coeffects
data CoeffectFold a = CoeffectFold
  { cNat   :: Int -> a
  , cFloat :: Rational -> a
  , cInf   :: Maybe (Type One) -> a
  , cInterval :: a -> a -> a
  , cVar   :: Id -> a
  , cPlus  :: a -> a -> a
  , cTimes :: a -> a -> a
  , cMinus :: a -> a -> a
  , cMeet  :: a -> a -> a
  , cJoin  :: a -> a -> a
  , cZero  :: Type One -> a
  , cOne   :: Type One -> a
  , cLevel :: Integer -> a
  , cSet   :: [(String, Type Zero)] -> a
  , cSig   :: a -> Type One -> a
  , cExpon :: a -> a -> a
  , cProd  :: a -> a -> a }

-- Base monadic algebra
baseCoeffectFold :: CoeffectFold Coeffect
baseCoeffectFold =
  CoeffectFold
    { cNat = CNat
    , cFloat = CFloat
    , cInf = CInfinity
    , cInterval = CInterval
    , cVar = CVar
    , cPlus = CPlus
    , cTimes = CTimes
    , cMinus = CMinus
    , cMeet = CMeet
    , cJoin = CJoin
    , cZero = CZero
    , cOne = COne
    , cLevel = Level
    , cSet = CSet
    , cSig = CSig
    , cExpon = CExpon
    , cProd = CProduct
    }

-- | Fold on a `coeffect` type
coeffectFold :: CoeffectFold a -> Coeffect -> a
coeffectFold algebra = go
  where
    go (CNat n) =
      (cNat algebra) n
    go (CFloat r) =
      (cFloat algebra) r
    go (CInfinity i) =
      (cInf algebra) i
    go (CInterval l u) = let
      l' = go l
      u' = go u
      in (cInterval algebra) l' u'
    go (CVar v) =
      (cVar algebra) v
    go (CPlus c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cPlus algebra) c1' c2'
    go (CTimes c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cTimes algebra) c1' c2'
    go (CMinus c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cMinus algebra) c1' c2'
    go (CMeet c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cMeet algebra) c1' c2'
    go (CJoin c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cJoin algebra) c1' c2'
    go (CZero t) =
      (cZero algebra) t
    go (COne t) =
      (cOne algebra) t
    go (Level l) =
      (cLevel algebra) l
    go (CSet set) =
      (cSet algebra) set
    go (CSig c t) = let
      c' = go c
      in (cSig algebra) c' t
    go (CExpon c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cExpon algebra) c1' c2'
    go (CProduct c1 c2) = let
      c1' = go c1
      c2' = go c2
      in (cProd algebra) c1' c2'

publicRepresentation, privateRepresentation :: Integer
privateRepresentation = 1
publicRepresentation  = 2

unusedRepresentation :: Integer
unusedRepresentation = 0

nat, extendedNat :: Type l
nat = TyCon $ mkId "Nat"
extendedNat = TyApp (TyCon $ mkId "Ext") (TyCon $ mkId "Nat")

infinity :: Coeffect
infinity = CInfinity (Just extendedNat)

isInterval :: Type l -> Maybe (Type l)
isInterval (TyApp (TyCon c) t) | internalName c == "Interval" = Just t
isInterval _ = Nothing

isProduct :: (Type l) -> Maybe (Type l, Type l)
isProduct (TyApp (TyApp (TyCon c) t) t') | internalName c == "×" =
    Just (t, t')
isProduct _ = Nothing

----------------------------------------------------------------------
-- Helpers

-- | Compute the arity of a function type
arity :: Type l -> Int
arity (FunTy _ _ t) = 1 + arity t
arity _           = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type l -> Type l
resultType (FunTy _ _ t) = resultType t
resultType t = t

-- | Get the leftmost type of an application
-- >>> leftmostOfApplication $ TyCon (mkId ",") .@ TyCon (mkId "Bool") .@ TyCon (mkId "Bool")
-- TyCon (Id "," ",")
leftmostOfApplication :: Type l -> Type l
leftmostOfApplication (TyApp t _) = leftmostOfApplication t
leftmostOfApplication t = t

-- | Smart constructor for type constructors
con :: String -> Type l
con = TyCon . mkId

-- | Smart constructor for type variables
var :: String -> Type l
var = TyVar . mkId

-- | Smart constructor for function types
(.->) :: Type l -> Type l -> Type l
s .-> t = FunTy Nothing s t
infixr 1 .->

-- | Smart constructor for type application
(.@) :: Type l -> Type l -> Type l
s .@ t = TyApp s t
infixl 9 .@

-- Trivially effectful monadic constructors
mTy :: Monad m => ULevel l -> m (Type (Succ l))
mTy          = return . Type
mFunTy :: Monad m => Maybe Id -> Type l -> Type l -> m (Type l)
mFunTy v x y   = return (FunTy v x y)
mTyCon :: Monad m => Id -> m (Type l)
mTyCon       = return . TyCon
mBox :: Monad m => Coeffect -> Type Zero -> m (Type Zero)
mBox c y     = return (Box c y)
mDiamond :: Monad m => Type Zero -> Type Zero -> m (Type Zero)
mDiamond e y = return (Diamond e y)
mTyVar :: Monad m => Id -> m (Type l)
mTyVar       = return . TyVar
mTyApp :: Monad m => Type l -> Type l -> m (Type l)
mTyApp x y   = return (TyApp x y)
mTyInt :: Monad m => Int -> m (Type l)
mTyInt       = return . TyInt
mTyInfix :: Monad m => TypeOperator -> Type l -> Type l -> m (Type l)
mTyInfix op x y  = return (TyInfix op x y)
mTySet   :: Monad m => [Type l] -> m (Type l)
mTySet xs    = return (TySet xs)
mTyCase :: Monad m => Type l -> [(Type l, Type l)] -> m (Type l)
mTyCase x cs = return (TyCase x cs)
mKUnion :: Monad m => Type Two -> Type Two -> m (Type Two)
mKUnion x y  = return (KUnion x y)
mTySig   :: Monad m => Type l -> Type l -> Type (Succ l) -> m (Type l)
mTySig t _ k      = return (TySig t k)


-- Monadic algebra for types
data TypeFold m (a :: Nat -> Haskell.Type) = TypeFold
  { tfTy      :: forall (l :: Nat) . ULevel l       -> m (a (Succ l))
  , tfFunTy   :: forall (l :: Nat) . Maybe Id -> a l -> a l -> m (a l)
  , tfTyCon   :: forall (l :: Nat) . Id            -> m (a l)
  , tfBox     :: Coeffect -> a Zero                -> m (a Zero)
  , tfDiamond :: a Zero -> a Zero                  -> m (a Zero)
  , tfTyVar   :: forall (l :: Nat) . Id            -> m (a l)
  , tfTyApp   :: forall (l :: Nat) . a l -> a l    -> m (a l)
  , tfTyInt   :: forall (l :: Nat) . Int           -> m (a l)
  , tfTyInfix :: forall (l :: Nat) . TypeOperator  -> a l -> a l -> m (a l)
  , tfSet     :: forall (l :: Nat) . [a l]         -> m (a l)
  , tfTyCase  :: forall (l :: Nat) . a l -> [(a l, a l)] -> m (a l)
  , tfKUnion  :: a Two -> a Two                    -> m (a Two)
  , tfTySig   :: forall (l :: Nat) . a l -> Type l -> (a (Succ l) -> m (a l))}

data TypeFoldAtLevel m (l :: Nat) (a :: Nat -> Haskell.Type) where
  TypeFoldZero ::
    { tfFunTy0   :: Maybe Id -> a Zero -> a Zero   -> m (a Zero)
    , tfTyCon0   :: Id                 -> m (a Zero)
    , tfBox0     :: Coeffect -> a Zero -> m (a Zero)
    , tfDiamond0 :: a Zero -> a Zero   -> m (a Zero)
    , tfTyVar0   :: Id                 -> m (a Zero)
    , tfTyApp0   :: a Zero -> a Zero   -> m (a Zero)
    , tfTyInt0   :: Int                -> m (a Zero)
    , tfTyInfix0 :: TypeOperator  -> a Zero -> a Zero -> m (a Zero)
    , tfSet0     :: [a Zero]           -> m (a Zero)
    , tfTyCase0  :: a Zero -> [(a Zero, a Zero)] -> m (a Zero)
    , tfTySig0   :: a Zero -> Type Zero -> Type (Succ Zero) -> m (a Zero)
    } -> TypeFoldAtLevel m Zero a

  TypeFoldOne ::
    { tfTy1      :: ULevel Zero        -> m (a One)
    , tfFunTy1   :: Maybe Id -> a One -> a One    -> m (a One)
    , tfTyCon1   :: Id                -> m (a One)
    , tfTyVar1   :: Id                -> m (a One)
    , tfTyApp1   :: a One -> a One    -> m (a One)
    , tfTyInt1   :: Int               -> m (a One)
    , tfTyInfix1 :: TypeOperator  -> a One -> a One -> m (a One)
    , tfSet1     :: [a One]           -> m (a One)
    , tfTyCase1  :: a One -> [(a One, a One)] -> m (a One)
    , tfTySig1   :: a One -> Type One -> Type (Succ (Succ Zero)) -> m (a One)
    } -> TypeFoldAtLevel m One a

  TypeFoldL ::
    { tfTyL      :: ULevel (Succ l)                     -> m (a (Succ (Succ l)))
    , tfFunTyL   :: Maybe Id -> a (Succ (Succ l)) -> a (Succ (Succ l))    -> m (a (Succ (Succ l)))
    , tfTyConL   :: Id                          -> m (a (Succ (Succ l)))
    , tfTyVarL   :: Id                          -> m (a (Succ (Succ l)))
    , tfTyAppL   :: a (Succ (Succ l)) -> a (Succ (Succ l))    -> m (a (Succ (Succ l)))
    , tfTyIntL   :: Int                         -> m (a (Succ (Succ l)))
    , tfTyInfixL :: TypeOperator  -> a (Succ (Succ l)) -> a (Succ (Succ l)) -> m (a (Succ (Succ l)))
    , tfSetL     :: [a (Succ (Succ l))]                -> m (a (Succ (Succ l)))
    , tfTyCaseL  :: a (Succ (Succ l)) -> [(a (Succ (Succ l)), a (Succ (Succ l)))] -> m (a (Succ (Succ l)))
    , tfKUnionL  :: a (Succ (Succ l)) -> a (Succ (Succ l))    -> m (a (Succ (Succ l)))
    , tfTySigL   :: a (Succ (Succ l)) -> Type (Succ (Succ l)) -> Type (Succ (Succ (Succ l))) -> m (a (Succ (Succ l)))
    } -> TypeFoldAtLevel m (Succ (Succ l)) a

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type --(Type l)
baseTypeFold =
  TypeFold mTy mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix mTySet mTyCase mKUnion mTySig

baseTypeFoldZero :: Monad m => TypeFoldAtLevel m Zero Type
baseTypeFoldZero =
  TypeFoldZero mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix mTySet mTyCase mTySig

baseTypeFoldOne :: Monad m => TypeFoldAtLevel m One Type
baseTypeFoldOne =
  TypeFoldOne mTy mFunTy mTyCon mTyVar mTyApp mTyInt mTyInfix mTySet mTyCase mTySig

-- | Monadic fold on a `Type` value
typeFoldM :: forall m l a . Monad m => TypeFold m a -> Type l -> m (a l)
typeFoldM algebra = go
  where
   go :: Type l' -> m (a l')
   go (Type l) = (tfTy algebra) l
   go (FunTy v t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy algebra) v t1' t2'
   go (TyCon s) = (tfTyCon algebra) s
   go (Box c t) = do
     t' <- go t
     (tfBox algebra) c t'
   go (Diamond e t) = do
     t' <- go t
     e' <- go e
     (tfDiamond algebra) e' t'
   go (TyVar v) = (tfTyVar algebra) v
   go (TyApp t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyApp algebra) t1' t2'
   go (TyInt i) = (tfTyInt algebra) i
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfix algebra) op t1' t2'
   go (TySet ts) = do
    ts' <- mapM go ts
    (tfSet algebra) ts'
   go (TySig t k) = do
     t' <- go t
     k' <- go k
     -- This part of the fold is a bit different:
     -- actually pass the original type in here as well
     (tfTySig algebra) t' t k'
   go (TyCase t ts) = do
    t' <- go t
    ts' <- mapM (\(a,b) -> extractMonad (go a, go b)) ts
    (tfTyCase algebra) t' ts'
    where
     extractMonad (a,b) = do
      a' <- a
      b' <- b
      return (a', b')
   go (KUnion t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfKUnion algebra) t1' t2'

-- | Monadic fold on a `Type` value
typeFoldM0 :: forall m a . Monad m => TypeFoldAtLevel m Zero a -> Type Zero -> m (a Zero)
typeFoldM0 algebra = go
  where
   go :: Type Zero -> m (a Zero)
   go (FunTy v t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy0 algebra) v t1' t2'
   go (TyCon s) = (tfTyCon0 algebra) s
   go (Box c t) = do
     t' <- go t
     (tfBox0 algebra) c t'
   go (Diamond e t) = do
     t' <- go t
     e' <- go e
     (tfDiamond0 algebra) e' t'
   go (TyVar v) = (tfTyVar0 algebra) v
   go (TyApp t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyApp0 algebra) t1' t2'
   go (TyInt i) = (tfTyInt0 algebra) i
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfix0 algebra) op t1' t2'
   go (TySet ts) = do
    ts' <- mapM go ts
    (tfSet0 algebra) ts'
   go (TyCase t ts) = do
    t' <- go t
    ts' <- mapM (\(a,b) -> extractMonad (go a, go b)) ts
    (tfTyCase0 algebra) t' ts'
    where
     extractMonad (a,b) = do
      a' <- a
      b' <- b
      return (a', b')
   go (TySig t k) = do
     t' <- go t
     -- This part of the fold is a bit different:
     -- actually pass the original type in here as well
     (tfTySig0 algebra) t' t k


-- | Monadic fold on a `Type` value
typeFoldM1 :: forall m a . Monad m => TypeFoldAtLevel m One a -> Type One -> m (a One)
typeFoldM1 algebra = go
  where
   go :: Type One -> m (a One)
   go (Type l) = (tfTy1 algebra) l
   go (FunTy v t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy1 algebra) v t1' t2'
   go (TyCon s) = (tfTyCon1 algebra) s
   go (TyVar v) = (tfTyVar1 algebra) v
   go (TyApp t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyApp1 algebra) t1' t2'
   go (TyInt i) = (tfTyInt1 algebra) i
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfix1 algebra) op t1' t2'
   go (TySet ts) = do
    ts' <- mapM go ts
    (tfSet1 algebra) ts'
   go (TyCase t ts) = do
    t' <- go t
    ts' <- mapM (\(a,b) -> extractMonad (go a, go b)) ts
    (tfTyCase1 algebra) t' ts'
    where
     extractMonad (a,b) = do
      a' <- a
      b' <- b
      return (a', b')
   go (TySig t k) = do
     t' <- go t
     -- This part of the fold is a bit different:
     -- actually pass the original type in here as well
     (tfTySig1 algebra) t' t k

typeFoldML :: forall m l a . Monad m => TypeFoldAtLevel m (Succ (Succ l)) a -> Type (Succ (Succ l)) -> m (a (Succ (Succ l)))
typeFoldML algebra = go
  where
   go :: Type (Succ (Succ l)) -> m (a (Succ (Succ l)))
   go (Type l) = (tfTyL algebra) l
   go (FunTy v t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTyL algebra) v t1' t2'
   go (TyCon s) = (tfTyConL algebra) s
   go (TyVar v) = (tfTyVarL algebra) v
   go (TyApp t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyAppL algebra) t1' t2'
   go (TyInt i) = (tfTyIntL algebra) i
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfixL algebra) op t1' t2'
   go (TySet ts) = do
    ts' <- mapM go ts
    (tfSetL algebra) ts'
   go (TyCase t ts) = do
    t' <- go t
    ts' <- mapM (\(a,b) -> extractMonad (go a, go b)) ts
    (tfTyCaseL algebra) t' ts'
    where
     extractMonad (a,b) = do
      a' <- a
      b' <- b
      return (a', b')
   go (KUnion t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfKUnionL algebra) t1' t2'
   go (TySig t k) = do
     t' <- go t
     -- This part of the fold is a bit different:
     -- actually pass the original type in here as well
     (tfTySigL algebra) t' t k

instance FirstParameter TypeScheme Span

freeAtomsVars :: Type l -> [Id]
freeAtomsVars (TyVar v) = [v]
freeAtomsVars (TyApp t1 (TyVar v)) = v : freeAtomsVars t1
freeAtomsVars (TyApp t1 _) = freeAtomsVars t1
freeAtomsVars t = []



----------------------------------------------------------------------
-- Types and coeffects are terms

instance Term (Type l) where
    freeVars = getConst . runIdentity . typeFoldM TypeFold
      { tfTy      = \_ -> return (Const [])
      , tfFunTy   = \_ (Const x) (Const y) -> return $ Const (x <> y)
      , tfTyCon   = \_ -> return (Const []) -- or: const (return [])
      , tfBox     = \c (Const t) -> return $ Const (freeVars c <> t)
      , tfDiamond = \(Const e) (Const t) -> return $ Const (e <> t)
      , tfTyVar   = \v -> return $ Const [v] -- or: return . return
      , tfTyApp   = \(Const x) (Const y) -> return $ Const (x <> y)
      , tfTyInt   = \_ -> return (Const [])
      , tfTyInfix = \_ (Const y) (Const z) -> return $ Const (y <> z)
      , tfSet     = return . Const . concat . map getConst
      , tfTyCase  = \(Const t) cs -> return . Const $ t <> (concat . concat) [[a,b] | (Const a, Const b) <- cs]
      , tfKUnion  = \(Const x) (Const y)   -> return $ Const (x <> y)
      , tfTySig   = \(Const t) _ (Const k) -> return $ Const (t <> k)
      }

    isLexicallyAtomic TyInt{} = True
    isLexicallyAtomic TyVar{} = True
    isLexicallyAtomic TySet{} = True
    isLexicallyAtomic TyCon{} = True
    isLexicallyAtomic (TyApp (TyApp (TyCon (sourceName -> ",")) _) _) = True
    isLexicallyAtomic _ = False

instance Term Coeffect where
    freeVars (CVar v) = [v]
    freeVars (CPlus c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CTimes c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CMinus c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CExpon c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CMeet c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CJoin c1 c2) = freeVars c1 <> freeVars c2
    freeVars CNat{}  = []
    freeVars CFloat{} = []
    freeVars CInfinity{} = []
    freeVars (CZero t) = freeVars t
    freeVars (COne t) = freeVars t
    freeVars Level{} = []
    freeVars CSet{} = []
    freeVars (CSig c k) = freeVars c <> freeVars k
    freeVars (CInterval c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CProduct c1 c2) = freeVars c1 <> freeVars c2

    isLexicallyAtomic CVar{} = True
    isLexicallyAtomic CNat{} = True
    isLexicallyAtomic CFloat{} = True
    isLexicallyAtomic CZero{} = True
    isLexicallyAtomic COne{} = True
    isLexicallyAtomic Level{} = True
    isLexicallyAtomic CProduct{} = True
    isLexicallyAtomic CInfinity{} = True
    isLexicallyAtomic _ = False


----------------------------------------------------------------------
-- Freshenable instances

instance Freshenable m TypeScheme where
  freshen :: Monad m => TypeScheme -> Freshener m TypeScheme
  freshen (Forall s binds constraints ty) = do
        binds' <- mapM (\(v, k) -> do { v' <- freshIdentifierBase TypeL v;
                                        k' <- freshen k;
                                        return (v', k') }) binds
        constraints' <- mapM freshen constraints
        ty' <- freshen ty
        return $ Forall s binds' constraints' ty'

instance Freshenable m (Type l) where
  freshen =
    typeFoldM (baseTypeFold { tfTyVar = freshenTyVar,
                              tfBox = freshenTyBox })
    where

      freshenTyBox c t = do
        c' <- freshen c
        t' <- freshen t
        return $ Box c' t'
      freshenTyVar v = do
        v' <- lookupVar TypeL v
        case v' of
           Just v' -> return (TyVar $ Id (sourceName v) v')
           -- This case happens if we are referring to a defined
           -- function which does not get its name freshened
           Nothing -> return (TyVar $ mkId (sourceName v))

instance Freshenable m Coeffect where
    freshen (CVar v) = do
      v' <- lookupVar TypeL v
      case v' of
        Just v' -> return $ CVar $ Id (sourceName v) v'
        Nothing -> return $ CVar v

    freshen (CInfinity (Just (TyVar i@(Id _ "")))) = do
      t <- freshIdentifierBase TypeL i
      return $ CInfinity $ Just $ TyVar t

    freshen (CPlus c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CPlus c1' c2'

    freshen (CTimes c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CTimes c1' c2'

    freshen (CMinus c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CMinus c1' c2'

    freshen (CExpon c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CExpon c1' c2'

    freshen (CMeet c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CMeet c1' c2'

    freshen (CJoin c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CJoin c1' c2'

    freshen (CSet cs) = do
       cs' <- mapM (\(s, t) -> freshen t >>= (\t' -> return (s, t'))) cs
       return $ CSet cs'
    freshen (CSig c k) = do
      c' <- freshen c
      k' <- freshen k
      return $ CSig c' k'
    freshen c@CInfinity{} = return c
    freshen c@CFloat{} = return c

    freshen (CZero t)  = do
      t' <- freshen t
      return $ CZero t'

    freshen (COne t)  = do
      t' <- freshen t
      return $ COne t'

    freshen c@Level{}  = return c
    freshen c@CNat{}   = return c
    freshen (CInterval c1 c2) = CInterval <$> freshen c1 <*> freshen c2
    freshen (CProduct c1 c2) = CProduct <$> freshen c1 <*> freshen c2

----------------------------------------------------------------------

-- | Normalise a coeffect using the semiring laws and some
--   local evaluation of natural numbers
--   There is plenty more scope to make this more comprehensive
--   None of this is stricly necessary but it improves type errors
--   and speeds up some constarint solving.
normalise :: Coeffect -> Coeffect
normalise (CPlus (CZero _) n) = normalise n
normalise (CPlus n (CZero _)) = normalise n
normalise (CTimes (COne _) n) = normalise n
normalise (CTimes n (COne _)) = normalise n
normalise (COne (TyCon (Id _ "Nat"))) = CNat 1
normalise (CZero (TyCon (Id _ "Nat"))) = CNat 0
normalise (COne (TyCon (Id _ "Level"))) = Level 1
normalise (CZero (TyCon (Id _ "Level"))) = Level 0
normalise (COne (TyCon (Id _ "Q"))) = CFloat 1
normalise (CZero (TyCon (Id _ "Q"))) = CFloat 0
normalise (COne (TyApp (TyCon (Id "Interval" "Interval")) t)) =
    (CInterval (normalise (COne t)) (normalise (COne t)))
normalise (CZero (TyApp (TyCon (Id "Interval" "Interval")) t)) =
        (CInterval (normalise (CZero t)) (normalise (CZero t)))

normalise (CPlus (Level n) (Level m)) = Level (n `max` m)
normalise (CTimes (Level n) (Level m)) = Level (n `min` m)
normalise (CPlus (CFloat n) (CFloat m)) = CFloat (n + m)
normalise (CTimes (CFloat n) (CFloat m)) = CFloat (n * m)
normalise (CPlus (CNat n) (CNat m)) = CNat (n + m)
normalise (CPlus n m) =
    if (n == n') && (m == m')
    then CPlus n m
    else normalise (CPlus n' m')
  where
    n' = normalise n
    m' = normalise m
normalise (CTimes n m) =
    if (n == n') && (m == m')
    then CTimes n m
    else normalise (CTimes n' m')
  where
    n' = normalise n
    m' = normalise m
-- Push signatures in
normalise (CSig (CPlus c1 c2) k) = CPlus (CSig (normalise c1) k) (CSig (normalise c2) k)
normalise (CSig (CTimes c1 c2) k) = CTimes (CSig (normalise c1) k) (CSig (normalise c2) k)
normalise (CSig (CMeet c1 c2) k) = CMeet (CSig (normalise c1) k) (CSig (normalise c2) k)
normalise (CSig (CJoin c1 c2) k) = CJoin (CSig (normalise c1) k) (CSig (normalise c2) k)
normalise (CSig (CNat 0) k) = CZero k
normalise (CSig (CZero _)  k) = CZero k
normalise (CSig (CNat 1) k) = COne k
normalise (CSig (COne _)   k) = CZero k
normalise (CSig (CInfinity _)  k) = CInfinity (Just k)

normalise c = c
