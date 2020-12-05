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

-- # Core representation

{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}

-- Aliases that can be useful in some places as documentation
type Coeffect = Type
type Effect   = Type
type Kind     = Type

-- | Type syntax (includes effect, coeffect, and predicate terms)
data Type where
    Type    :: Int -> Type                          -- ^ Universe construction
    FunTy   :: Maybe Id -> Type -> Type -> Type     -- ^ Function type

    TyCon   :: Id -> Type                           -- ^ Type constructor
    Box     :: Coeffect -> Type -> Type             -- ^ Graded modal necessity
    Diamond :: Effect   -> Type -> Type             -- ^ Graded modal possibility
    TyVar   :: Id -> Type                           -- ^ Type variable
    TyApp   :: Type -> Type -> Type                 -- ^ Type application
    TyInt   :: Int -> Type                          -- ^ Type-level Int
    TyRational :: Rational -> Type                  -- ^ Type-level Rational
    TyGrade :: Maybe Type -> Int -> Type            -- ^ Graded element
    TyInfix :: TypeOperator -> Type -> Type -> Type -- ^ Infix type operator

    TySet   :: [Type] -> Type                 -- ^ Type-level set
    TyCase  :: Type -> [(Type, Type)] -> Type -- ^ Type-level case

    TySig   :: Type -> Kind -> Type           -- ^ Kind signature

deriving instance Show Type
deriving instance Eq Type
deriving instance Ord Type
deriving instance Data Type
deriving instance Typeable Type

-- Constructors and operators are just strings
data TypeOperator
  = TyOpLesserNat
  | TyOpLesserEq
  | TyOpLesserEqNat
  | TyOpGreaterNat
  | TyOpGreaterEq
  | TyOpGreaterEqNat
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

-- ## Type schemes

-- | Represent types with a universal quantification at the start
data TypeScheme =
  Forall
    Span          -- span of the scheme
    [(Id, Kind)]  -- binders
    [Type]      -- constraints
    Type      -- type
  deriving (Eq, Show, Generic, Data)

instance FirstParameter TypeScheme Span

trivialScheme :: Type -> TypeScheme
trivialScheme = Forall nullSpanNoFile [] []

unforall :: TypeScheme -> Type
unforall (Forall _ _ _ t) = t

----------------------------------------------------------------------
-- # Smart constructors

-- | Smart constructors for function types
funTy :: Type -> Type -> Type
funTy = FunTy Nothing

(.->) :: Type -> Type -> Type
s .-> t = FunTy Nothing s t
infixr 1 .->

-- | Smart constructor for constructors and variable
tyCon :: String -> Type
tyCon = TyCon . mkId

tyVar :: String -> Type
tyVar = TyVar . mkId

-- | Smart constructor for type application
(.@) :: Type -> Type -> Type
s .@ t = TyApp s t
infixl 9 .@

-- | Smart constructors for constants and things at different levels

ktype :: Type
ktype = Type 0

kcoeffect :: Type
kcoeffect = tyCon "Coeffect"

keffect :: Type
keffect = tyCon "Effect"

kpredicate :: Type
kpredicate = tyCon "Predicate"

kNat, protocol :: Type
kNat     = tyCon "Nat"
protocol = tyCon "Protocol"

publicRepresentation, privateRepresentation :: Integer
privateRepresentation = 1
publicRepresentation  = 2

unusedRepresentation :: Integer
unusedRepresentation = 0

nat, extendedNat :: Type
nat = tyCon "Nat"
extendedNat = TyApp (tyCon "Ext") (tyCon "Nat")

level :: Type
level = tyCon "Level"

infinity :: Type
infinity = tyCon "Infinity"

isInterval :: Type -> Maybe Type
isInterval (TyApp (TyCon c) t) | internalName c == "Interval" = Just t
isInterval _ = Nothing

isProduct :: Type -> Maybe (Type, Type)
isProduct (TyApp (TyApp (TyCon c) t) t') | internalName c == "×" || internalName c == "," =
    Just (t, t')
isProduct _ = Nothing

----------------------------------------------------------------------
-- # Helpers

-- Calculate whether a type could be used a generic semiring/grade expression
isGenericCoeffectExpression :: Type -> Bool
isGenericCoeffectExpression (TyGrade Nothing _) = True
isGenericCoeffectExpression (TyInfix TyOpPlus c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpTimes c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpMeet c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpJoin c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression _ = False

-- Contains signature?
containsTypeSig :: Type -> Bool
containsTypeSig =
  runIdentity . typeFoldM (TypeFold
      { tfTy = \_ -> return $ False
      , tfFunTy = \_ x y -> return (x || y)
      , tfTyCon = \_ -> return False
      , tfBox = \x y -> return (x || y)
      , tfDiamond = \x y -> return $ (x || y)
      , tfTyVar = \_ -> return False
      , tfTyApp = \x y -> return (x || y)
      , tfTyInt = \_ -> return False
      , tfTyRational = \_ -> return False
      , tfTyGrade = \_ _ -> return False
      , tfTyInfix = \_ x y -> return (x || y)
      , tfSet = \_ -> return  False
      , tfTyCase = \_ _ -> return False
      , tfTySig = \_ _ _ -> return True })

-- | Compute the arity of a function type
arity :: Type -> Int
arity (FunTy _ _ t) = 1 + arity t
arity _           = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type -> Type
resultType (FunTy _ _ t) = resultType t
resultType t = t

parameterTypes :: Type -> [Type]
parameterTypes (FunTy _ t1 t2) = t1 : parameterTypes t2
parameterTypes t               = []

-- | Get the leftmost type of an application
-- >>> leftmostOfApplication $ TyCon (mkId ",") .@ TyCon (mkId "Bool") .@ TyCon (mkId "Bool")
-- TyCon (Id "," ",")
leftmostOfApplication :: Type -> Type
leftmostOfApplication (TyApp t _) = leftmostOfApplication t
leftmostOfApplication t = t

freeAtomsVars :: Type -> [Id]
freeAtomsVars (TyVar v) = [v]
freeAtomsVars (TyApp t1 (TyVar v)) = v : freeAtomsVars t1
freeAtomsVars (TyApp t1 _) = freeAtomsVars t1
freeAtomsVars t = []

----------------------------------------------------------------------
-- # Type fold


-- Trivially effectful monadic constructors
mTy :: Monad m => Int -> m Type
mTy          = return . Type
mFunTy :: Monad m => Maybe Id -> Type -> Type -> m Type
mFunTy v x y   = return (FunTy v x y)
mTyCon :: Monad m => Id -> m Type
mTyCon       = return . TyCon
mBox :: Monad m => Coeffect -> Type -> m Type
mBox c y     = return (Box c y)
mDiamond :: Monad m => Type -> Type -> m Type
mDiamond e y = return (Diamond e y)
mTyVar :: Monad m => Id -> m Type
mTyVar       = return . TyVar
mTyApp :: Monad m => Type -> Type -> m Type
mTyApp x y   = return (TyApp x y)
mTyInt :: Monad m => Int -> m Type
mTyInt       = return . TyInt
mTyRational :: Monad m => Rational -> m Type
mTyRational          = return . TyRational
mTyGrade :: Monad m => Maybe Type -> Int -> m Type
mTyGrade t c = return $ TyGrade t c
mTyInfix :: Monad m => TypeOperator -> Type -> Type -> m Type
mTyInfix op x y  = return (TyInfix op x y)
mTySet   :: Monad m => [Type] -> m Type
mTySet xs    = return (TySet xs)
mTyCase :: Monad m => Type -> [(Type, Type)] -> m Type
mTyCase x cs = return (TyCase x cs)
mTySig   :: Monad m => Type -> Type -> Type -> m Type
mTySig t _ k      = return (TySig t k)

-- Monadic algebra for types
data TypeFold m a = TypeFold
  { tfTy      :: Int                -> m a
  , tfFunTy   :: Maybe Id -> a -> a -> m a
  , tfTyCon   :: Id                 -> m a
  , tfBox     :: a -> a             -> m a
  , tfDiamond :: a -> a             -> m a
  , tfTyVar   :: Id                 -> m a
  , tfTyApp   :: a -> a             -> m a
  , tfTyInt   :: Int                -> m a
  , tfTyRational :: Rational        -> m a
  , tfTyGrade :: Maybe a   -> Int  -> m a
  , tfTyInfix :: TypeOperator -> a -> a -> m a
  , tfSet     :: [a]                -> m a
  , tfTyCase  :: a -> [(a, a)]      -> m a
  , tfTySig   :: a -> Type -> (a -> m a)
  }

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type --Type
baseTypeFold =
  TypeFold mTy mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyRational mTyGrade mTyInfix mTySet mTyCase mTySig

-- | Monadic fold on a `Type` value
typeFoldM :: forall m a . Monad m => TypeFold m a -> Type -> m a
typeFoldM algebra = go
  where
   go :: Type -> m a
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
   go (TyGrade Nothing i) = (tfTyGrade algebra) Nothing i
   go (TyGrade (Just t) i) = do
     t' <- go t
     (tfTyGrade algebra) (Just t') i
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

----------------------------------------------------------------------
-- # Types are terms

instance Term Type where
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
      , tfTyGrade     = \_ _ -> return (Const [])
      , tfTyInfix = \_ (Const y) (Const z) -> return $ Const (y <> z)
      , tfSet     = return . Const . concat . map getConst
      , tfTyCase  = \(Const t) cs -> return . Const $ t <> (concat . concat) [[a,b] | (Const a, Const b) <- cs]
      , tfTySig   = \(Const t) _ (Const k) -> return $ Const (t <> k)
      }

    isLexicallyAtomic TyInt{} = True
    isLexicallyAtomic TyRational{} = True
    isLexicallyAtomic TyGrade{} = True
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

instance Freshenable m Type where
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
normalise :: Type -> Type
normalise (TyInfix TyOpPlus (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `max` m)
normalise (TyInfix TyOpTimes (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `min` m)
normalise (TyInfix TyOpPlus (TyRational n) (TyRational m)) = TyRational (n + m)
normalise (TyInfix TyOpTimes (TyRational n) (TyRational m)) = TyRational (n * m)
normalise (TyInfix TyOpPlus (TyGrade k n) (TyGrade k' m)) | k == k' = TyGrade k (n + m)
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
