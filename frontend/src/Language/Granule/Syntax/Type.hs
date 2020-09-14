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

-- Syntax of types

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

-- # Core representation

{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}

-- Aliases
-- type Type = Type Zero [philosophically, but name spaces don't allow it]
type Coeffect = Type Zero
type Effect   = Type Zero
type Kind     = Type One

-- | Type syntax (includes effect, coeffect, and predicate terms)
data Type (l :: Nat) where
    Type    :: ULevel l -> Type (Succ l)                -- ^ Universe construction
    FunTy   :: Maybe Id -> Type l  -> Type l -> Type l  -- ^ Function type

    TyCon   :: Id -> Type l                          -- ^ Type constructor
    Box     :: Coeffect -> Type Zero -> Type Zero    -- ^ Coeffect type
    Diamond :: Effect   -> Type Zero -> Type Zero    -- ^ Effect type
    TyVar   :: Id -> Type l                          -- ^ Type variable
    TyApp   :: Type l -> Type l -> Type l            -- ^ Type application
    TyInt   :: Int -> Type l                         -- ^ Type-level Int
    TyRational :: Rational -> Type l                 -- ^ Type-level Rational
    TyInfix :: TypeOperator -> Type l -> Type l -> Type l -- ^ Infix type operator

    TySet   :: [Type l] -> Type l                     -- ^ Type-level set
    TyCase  :: Type l -> [(Type l, Type l)] -> Type l -- ^ Type-level case

    TySig   :: Type l -> Type (Succ l) -> Type l      -- ^ Kind signature

deriving instance Show (Type l)
deriving instance Eq (Type l)
deriving instance Ord (Type l)
deriving instance Typeable (Type l)

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
  | TyOpInterval
  deriving (Eq, Ord, Show, Data)

-- ## Levels

type One = Succ Zero
type Two = Succ One

data Nat = Succ Nat | Zero
 deriving Eq

data ULevel (l :: Nat) where
  LSucc :: ULevel l -> ULevel (Succ l)
  LZero :: ULevel Zero

data IsLevel where
  IsLevel :: ULevel l -> IsLevel

deriving instance Show IsLevel

class LesserLevel (l :: Nat) (l' :: Nat) where
  typePromote :: Type l -> Maybe (Type l')

instance HasLevel l => LesserLevel Zero (Succ l) where
  typePromote (FunTy v t1 t2) = do
    t1 <- typePromote t1
    t2 <- typePromote t2
    return $ FunTy v t1 t2
  typePromote (TyCon i) = return $ TyCon i
  typePromote (TyVar i) = return $ TyVar i
  typePromote (TyApp t1 t2) = do
    t1 <- typePromote t1
    t2 <- typePromote t2
    return $ TyApp t1 t2
  typePromote (TyInt n) = return $ TyInt n
  typePromote (TyInfix op t1 t2) = do
    t1 <- typePromote t1
    t2 <- typePromote t2
    return $ TyInfix op t1 t2
  typePromote (TySet ts) = do
    ts <- mapM typePromote ts
    return $ TySet ts
  typePromote (TyCase t ts) = do
    t <- typePromote t
    ts <- mapM (\(a,b) -> (,) <$> (typePromote a) <*> (typePromote b)) ts
    return $ TyCase t ts
  typePromote t = Nothing


-- instance LesserLevel l l' => LesserLevel (Succ l) (Succ l')

deriving instance Eq (ULevel l)
deriving instance Show (ULevel l)
deriving instance Ord (ULevel l)

-- ## Type schemes

-- | Represent types with a universal quantification at the start
data TypeScheme =
  Forall
    Span          -- span of the scheme
    [(Id, Kind)]  -- binders
    [Type Zero]      -- constraints
    (Type Zero)      -- type
  deriving (Eq, Show, Generic, Data)

instance FirstParameter TypeScheme Span

trivialScheme :: Type Zero -> TypeScheme
trivialScheme = Forall nullSpanNoFile [] []

unforall :: TypeScheme -> Type Zero
unforall (Forall _ _ _ t) = t

-------------------------------------------

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
  ts <- mapM (\(a,b) -> (,) <$> (tyPromote a) <*> (tyPromote b)) ts
  return $ TyCase t ts
tyPromote t = Nothing

-- ## Notion of a type with an (existential) level

data TypeWithLevel where
  TypeWithLevel :: ULevel l -> Type l -> TypeWithLevel

deriving instance Show TypeWithLevel

-- This is only used for testing and should really be avoided
-- elsewhere
instance Eq TypeWithLevel where
  (TypeWithLevel u t) == (TypeWithLevel u' t') =
    (show u == show u') && (show t == show t')

instance Typeable l => Data (Type l) where
  gunfold    = gunfold
  toConstr   = error "Internal bug: Cannot use a Data instance on `Type l` yet"
  dataTypeOf = error "Internal bug: Cannot use a Data instance on `Type l` yet"

data LevelProxy (l :: Nat) = LevelProxy

typeWithLevel :: forall l . HasLevel l => Type l -> TypeWithLevel
typeWithLevel t = TypeWithLevel (getLevel t) t

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

----------------------------------------------------------------------
-- # Smart constructors

-- | Smart constructors for function types
funTy :: Type l -> Type l -> Type l
funTy = FunTy Nothing

(.->) :: Type l -> Type l -> Type l
s .-> t = FunTy Nothing s t
infixr 1 .->

-- | Smart constructor for constructors and variable
tyCon :: String -> Type l
tyCon = TyCon . mkId

tyVar :: String -> Type l'
tyVar = TyVar . mkId

-- | Smart constructor for type application
(.@) :: Type l -> Type l -> Type l
s .@ t = TyApp s t
infixl 9 .@

-- | Smart constructors for constants and things at different levels

type0 :: Type Zero -> TypeWithLevel
type0 = TypeWithLevel LZero

ktype :: Kind
ktype     = tyCon "Type"

kcoeffect :: Type Two
kcoeffect = tyCon "Coeffect"

keffect :: Type Two
keffect   = tyCon "Effect"

kpredicate :: Kind
kpredicate = tyCon "Predicate"

kNat, protocol :: Kind
kNat = TyCon $ mkId "Nat"
protocol = TyCon $ mkId "Protocol"

publicRepresentation, privateRepresentation :: Integer
privateRepresentation = 1
publicRepresentation  = 2

unusedRepresentation :: Integer
unusedRepresentation = 0

nat, extendedNat :: Type l
nat = TyCon $ mkId "Nat"
extendedNat = TyApp (TyCon $ mkId "Ext") (TyCon $ mkId "Nat")

level :: Type l
level = TyCon (mkId "Level")

infinity :: Type l
infinity = TyCon (mkId "Infinity")

isInterval :: Type l -> Maybe (Type l)
isInterval (TyApp (TyCon c) t) | internalName c == "Interval" = Just t
isInterval _ = Nothing

isProduct :: Type l -> Maybe (Type l, Type l)
isProduct (TyApp (TyApp (TyCon c) t) t') | internalName c == "×" || internalName c == "," =
    Just (t, t')
isProduct _ = Nothing

----------------------------------------------------------------------
-- # Helpers

-- | Compute the arity of a function type
arity :: Type l -> Int
arity (FunTy _ _ t) = 1 + arity t
arity _           = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type l -> Type l
resultType (FunTy _ _ t) = resultType t
resultType t = t

parameterTypes :: Type l -> [Type l]
parameterTypes (FunTy _ t1 t2) = t1 : parameterTypes t2
parameterTypes t               = []

-- | Get the leftmost type of an application
-- >>> leftmostOfApplication $ TyCon (mkId ",") .@ TyCon (mkId "Bool") .@ TyCon (mkId "Bool")
-- TyCon (Id "," ",")
leftmostOfApplication :: Type l -> Type l
leftmostOfApplication (TyApp t _) = leftmostOfApplication t
leftmostOfApplication t = t

freeAtomsVars :: Type l -> [Id]
freeAtomsVars (TyVar v) = [v]
freeAtomsVars (TyApp t1 (TyVar v)) = v : freeAtomsVars t1
freeAtomsVars (TyApp t1 _) = freeAtomsVars t1
freeAtomsVars t = []

----------------------------------------------------------------------
-- # Type fold


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
mTyRational :: Monad m => Rational -> m (Type l)
mTyRational          = return . TyRational
mTyInfix :: Monad m => TypeOperator -> Type l -> Type l -> m (Type l)
mTyInfix op x y  = return (TyInfix op x y)
mTySet   :: Monad m => [Type l] -> m (Type l)
mTySet xs    = return (TySet xs)
mTyCase :: Monad m => Type l -> [(Type l, Type l)] -> m (Type l)
mTyCase x cs = return (TyCase x cs)
mTySig   :: Monad m => Type l -> Type l -> Type (Succ l) -> m (Type l)
mTySig t _ k      = return (TySig t k)

-- Monadic algebra for types
data TypeFold m (a :: Nat -> Haskell.Type) = TypeFold
  { tfTy      :: forall (l :: Nat) . ULevel l       -> m (a (Succ l))
  , tfFunTy   :: forall (l :: Nat) . Maybe Id -> a l -> a l -> m (a l)
  , tfTyCon   :: forall (l :: Nat) . Id            -> m (a l)
  , tfBox     :: a Zero -> a Zero                  -> m (a Zero)
  , tfDiamond :: a Zero -> a Zero                  -> m (a Zero)
  , tfTyVar   :: forall (l :: Nat) . Id            -> m (a l)
  , tfTyApp   :: forall (l :: Nat) . a l -> a l    -> m (a l)
  , tfTyInt   :: forall (l :: Nat) . Int           -> m (a l)
  , tfTyRational :: forall (l :: Nat) . Rational   -> m (a l)
  , tfTyInfix :: forall (l :: Nat) . TypeOperator  -> a l -> a l -> m (a l)
  , tfSet     :: forall (l :: Nat) . [a l]         -> m (a l)
  , tfTyCase  :: forall (l :: Nat) . a l -> [(a l, a l)] -> m (a l)
  , tfTySig   :: forall (l :: Nat) . a l -> Type l -> (a (Succ l) -> m (a l))}

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type --(Type l)
baseTypeFold =
  TypeFold mTy mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyRational mTyInfix mTySet mTyCase mTySig

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
     c' <- go c
     t' <- go t
     (tfBox algebra) c' t'
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
   go (TyRational i) = (tfTyRational algebra) i
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

data TypeFoldAtLevel m (l :: Nat) (a :: Nat -> Haskell.Type) where
  TypeFoldZero ::
    { tfFunTy0   :: Maybe Id -> a Zero -> a Zero   -> m (a Zero)
    , tfTyCon0   :: Id                 -> m (a Zero)
    , tfBox0     :: Coeffect -> a Zero -> m (a Zero)
    , tfDiamond0 :: a Zero -> a Zero   -> m (a Zero)
    , tfTyVar0   :: Id                 -> m (a Zero)
    , tfTyApp0   :: a Zero -> a Zero   -> m (a Zero)
    , tfTyInt0   :: Int                -> m (a Zero)
    , tfTyRational0   :: Rational      -> m (a Zero)
    , tfTyInfix0 :: TypeOperator  -> a Zero -> a Zero -> m (a Zero)
    , tfSet0     :: [a Zero]           -> m (a Zero)
    , tfTyCase0  :: a Zero -> [(a Zero, a Zero)] -> m (a Zero)
    , tfTySig0   :: a Zero -> Type Zero -> Type (Succ Zero) -> m (a Zero)
    } -> TypeFoldAtLevel m Zero a

baseTypeFoldZero :: Monad m => TypeFoldAtLevel m Zero Type
baseTypeFoldZero =
  TypeFoldZero mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyRational mTyInfix mTySet mTyCase mTySig

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
   go (TyRational i) = (tfTyRational0 algebra) i
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


----------------------------------------------------------------------
-- # Types are terms

instance Term (Type l) where
    freeVars = getConst . runIdentity . typeFoldM TypeFold
      { tfTy      = \_ -> return (Const [])
      , tfFunTy   = \_ (Const x) (Const y) -> return $ Const (x <> y)
      , tfTyCon   = \_ -> return (Const []) -- or: const (return [])
      , tfBox     = \(Const c) (Const t) -> return $ Const (c <> t)
      , tfDiamond = \(Const e) (Const t) -> return $ Const (e <> t)
      , tfTyVar   = \v -> return $ Const [v] -- or: return . return
      , tfTyApp   = \(Const x) (Const y) -> return $ Const (x <> y)
      , tfTyInt   = \_ -> return (Const [])
      , tfTyRational  = \_ -> return (Const [])
      , tfTyInfix = \_ (Const y) (Const z) -> return $ Const (y <> z)
      , tfSet     = return . Const . concat . map getConst
      , tfTyCase  = \(Const t) cs -> return . Const $ t <> (concat . concat) [[a,b] | (Const a, Const b) <- cs]
      , tfTySig   = \(Const t) _ (Const k) -> return $ Const (t <> k)
      }

    isLexicallyAtomic TyInt{} = True
    isLexicallyAtomic TyRational{} = True
    isLexicallyAtomic TyVar{} = True
    isLexicallyAtomic TySet{} = True
    isLexicallyAtomic TyCon{} = True
    isLexicallyAtomic (TyApp (TyApp (TyCon (sourceName -> ",")) _) _) = True
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
                              tfBox = freshenTyBox,
                              tfTySig = freshenTySig })
    where

      freshenTyBox c t = do
        c' <- freshen c
        t' <- freshen t
        return $ Box c' t'

      freshenTySig t' _ k = do
        k' <- freshen k
        return $TySig t' k'

      freshenTyVar v = do
        v' <- lookupVar TypeL v
        case v' of
           Just v' -> return (TyVar $ Id (sourceName v) v')
           -- This case happens if we are referring to a defined
           -- function which does not get its name freshened
           Nothing -> return (TyVar $ mkId (sourceName v))

----------------------------------------------------------------------

-- | Normalise a coeffect using the semiring laws and some
--   local evaluation of natural numbers
--   There is plenty more scope to make this more comprehensive
--   None of this is stricly necessary but it improves type errors
--   and speeds up some constarint solving.
normalise :: Type l -> Type l
normalise (TyInfix TyOpPlus (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `max` m)
normalise (TyInfix TyOpTimes (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `min` m)
normalise (TyInfix TyOpPlus (TyRational n) (TyRational m)) = TyRational (n + m)
normalise (TyInfix TyOpTimes (TyRational n) (TyRational m)) = TyRational (n * m)
normalise (TyInfix TyOpPlus (TyInt n) (TyInt m)) = TyInt (n + m)
normalise (TyInfix TyOpTimes (TyInt n) (TyInt m)) = TyInt (n * m)
normalise (TyInfix TyOpPlus n m) =
    if (n == n') && (m == m')
    then TyInfix TyOpPlus n m
    else normalise (TyInfix TyOpPlus n' m')
  where
    n' = normalise n
    m' = normalise m
normalise (TyInfix TyOpTimes n m) =
    if (n == n') && (m == m')
    then TyInfix TyOpTimes n m
    else normalise (TyInfix TyOpTimes n' m')
  where
    n' = normalise n
    m' = normalise m
-- Push signatures in
normalise (TySig (TyInfix TyOpPlus c1 c2) k) = TyInfix TyOpPlus (TySig (normalise c1) k) (TySig (normalise c2) k)
normalise (TySig (TyInfix TyOpTimes c1 c2) k) = TyInfix TyOpTimes (TySig (normalise c1) k) (TySig (normalise c2) k)
normalise (TySig (TyInfix TyOpMeet c1 c2) k) = TyInfix TyOpMeet (TySig (normalise c1) k) (TySig (normalise c2) k)
normalise (TySig (TyInfix TyOpJoin c1 c2) k) = TyInfix TyOpJoin (TySig (normalise c1) k) (TySig (normalise c2) k)
normalise c = c
