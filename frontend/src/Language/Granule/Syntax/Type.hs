{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

-- Syntax of types, coeffects, and effects

module Language.Granule.Syntax.Type where

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

import Data.Functor.Identity (Identity, runIdentity)
import GHC.Generics (Generic)
import qualified Text.Reprinter as Rp (Data)

-- | Represent types with a universal quantification at the start
data TypeScheme =
  Forall
    Span          -- span of the scheme
    [(Id, Kind)]  -- binders
    [Type]        -- constraints
    Type          -- type
  deriving (Eq, Show, Generic, Rp.Data)

trivialScheme :: Type -> TypeScheme
trivialScheme = Forall nullSpanNoFile [] []

unforall :: TypeScheme -> Type
unforall (Forall _ _ _ t) = t

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
  deriving (Eq, Ord, Show, Rp.Data)


{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy (Maybe Id) Type Type      -- ^ Function type
          | TyCon Id                        -- ^ Type constructor
          | Box Type Type                   -- ^ Coeffect type
          | Diamond Type Type               -- ^ Effect type
          | TyVar Id                        -- ^ Type variable
          | TyApp Type Type                 -- ^ Type application
          | TyInt Int                       -- ^ Type-level Int
          | TyInfix TypeOperator Type Type  -- ^ Infix type operator
          | TySet [Type]                    -- ^ Type-level set
          | TySig Type Kind                 -- ^ Signature
          | TyFloat Rational                -- ^ Type-level Float
    deriving (Eq, Ord, Show, Rp.Data)

-- | Kinds
data Kind = KType
          | KCoeffect
          | KEffect
          | KPredicate
          | KFun Kind Kind
          | KVar Id              -- Kind poly variable
          | KPromote Type        -- Promoted types
          | KUnion Kind Kind
    deriving (Show, Ord, Eq, Rp.Data)

promoteTypeToKind :: Type -> Kind
promoteTypeToKind (TyVar v) = KVar v
promoteTypeToKind t = KPromote t

demoteKindToType :: Kind -> Maybe Type
demoteKindToType (KPromote t) = Just t
demoteKindToType (KVar v)     = Just (TyVar v)
demoteKindToType _            = Nothing

instance Term Kind where
  freeVars (KPromote t) = freeVars t
  freeVars (KVar x)     = [x]
  freeVars _            = []

  isLexicallyAtomic KVar{} = True
  isLexicallyAtomic KType{} = True
  isLexicallyAtomic KCoeffect{} = True
  isLexicallyAtomic KEffect{} = True
  isLexicallyAtomic KPredicate{} = True
  isLexicallyAtomic KPromote{} = True
  isLexicallyAtomic _ = False

kConstr :: Id -> Kind
kConstr = KPromote . TyCon

kNat, protocol :: Kind
kNat = kConstr $ mkId "Nat"
protocol = kConstr $ mkId "Protocol"

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
    v' <- lookupVar  Type v
    case v' of
       Just v' -> return (KVar $ Id (sourceName v) v')
       -- This case happens if we are referring to a defined
       -- function which does not get its name freshened
       Nothing -> return (KVar $ mkId (sourceName v))

  freshen (KPromote ty) = do
     ty <- freshen ty
     return $ KPromote ty

  freshen (KUnion k1 k2) = do
    k1' <- freshen k1
    k2' <- freshen k2
    return $ KUnion k1' k2'

publicRepresentation, privateRepresentation :: Integer
privateRepresentation = 1
publicRepresentation  = 2

unusedRepresentation :: Integer
unusedRepresentation = 0

nat, extendedNat :: Type
nat = TyCon $ mkId "Nat"
extendedNat = TyApp (TyCon $ mkId "Ext") (TyCon $ mkId "Nat")

infinity :: Type
infinity = TyCon (mkId "Infinity")

isInterval :: Type -> Maybe Type
isInterval (TyApp (TyCon c) t) | internalName c == "Interval" = Just t
isInterval _ = Nothing

isProduct :: Type -> Maybe (Type, Type)
isProduct (TyApp (TyApp (TyCon c) t) t') | internalName c == "×" || internalName c == "," =
    Just (t, t')
isProduct _ = Nothing

----------------------------------------------------------------------
-- Helpers

-- | Natural numbers
type Nat = Word

-- | Compute the arity of a function type
arity :: Type -> Nat
arity (FunTy _ _ t) = 1 + arity t
arity _             = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type -> Type
resultType (FunTy _ _ t) = resultType t
resultType t = t

resultKind :: Kind -> Kind
resultKind (KFun _ k) = resultKind k
resultKind k = k

parameterTypes :: Type -> [Type]
parameterTypes (FunTy _ t1 t2) = t1 : parameterTypes t2
parameterTypes t               = []

parameterKinds :: Kind -> [Kind]
parameterKinds (KFun k1 k2) = k1 : parameterKinds k2
parameterKinds t            = []

-- | Get the leftmost type of an application
-- >>> leftmostOfApplication $ TyCon (mkId ",") .@ TyCon (mkId "Bool") .@ TyCon (mkId "Bool")
-- TyCon (Id "," ",")
leftmostOfApplication :: Type -> Type
leftmostOfApplication (TyApp t _) = leftmostOfApplication t
leftmostOfApplication t = t

-- | Smart constructor for type constructors
con :: String -> Type
con = TyCon . mkId

-- | Smart constructor for type variables
var :: String -> Type
var = TyVar . mkId

-- | Smart constructor for function types
(.->) :: Type -> Type -> Type
s .-> t = FunTy Nothing s t
infixr 1 .->

-- | Smart constructor for type application
(.@) :: Type -> Type -> Type
s .@ t = TyApp s t
infixl 9 .@

-- Trivially effectful monadic constructors
mFunTy :: Monad m => Maybe Id -> Type -> Type -> m Type
mFunTy id x y   = return (FunTy id x y)
mTyCon :: Monad m => Id -> m Type
mTyCon          = return . TyCon
mBox :: Monad m => Type -> Type -> m Type
mBox c y        = return (Box c y)
mDiamond :: Monad m => Type -> Type -> m Type
mDiamond e y    = return (Diamond e y)
mTyVar :: Monad m => Id -> m Type
mTyVar          = return . TyVar
mTyApp :: Monad m => Type -> Type -> m Type
mTyApp x y      = return (TyApp x y)
mTyInt :: Monad m => Int -> m Type
mTyInt          = return . TyInt
mTyInfix :: Monad m => TypeOperator -> Type -> Type -> m Type
mTyInfix op x y = return (TyInfix op x y)
mTySet   :: Monad m => [Type] -> m Type
mTySet xs       = return (TySet xs)
mTySig   :: Monad m => Type -> Type -> Kind -> m Type
mTySig t _ k      = return (TySig t k)
mTyFloat :: Monad m => Rational -> m Type
mTyFloat          = return . TyFloat

-- Monadic algebra for types
data TypeFold m a = TypeFold
  { tfFunTy   :: Maybe Id -> a -> a     -> m a
  , tfTyCon   :: Id                     -> m a
  , tfBox     :: Type -> a              -> m a
  , tfDiamond :: a -> a                 -> m a
  , tfTyVar   :: Id                     -> m a
  , tfTyApp   :: a -> a                 -> m a
  , tfTyInt   :: Int                    -> m a
  , tfTyInfix :: TypeOperator -> a -> a -> m a
  , tfSet     :: [a]                    -> m a
  , tfTySig   :: a -> Type -> Kind      -> m a
  , tfTyFloat :: Rational               -> m a }

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type
baseTypeFold =
  TypeFold mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix mTySet mTySig mTyFloat

-- | Monadic fold on a `Type` value
typeFoldM :: Monad m => TypeFold m a -> Type -> m a
typeFoldM algebra = go
  where
   go (FunTy id t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy algebra) id t1' t2'
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
     -- This part of the fold is a bit different:
     -- actually pass the original type in here as well
     (tfTySig algebra) t' t k
   go (TyFloat f) = tfTyFloat algebra f

typeFold :: TypeFold Identity a -> Type -> a
typeFold algebra = runIdentity . typeFoldM algebra

instance FirstParameter TypeScheme Span

freeAtomsVars :: Type -> [Id]
freeAtomsVars (TyVar v) = [v]
freeAtomsVars (TyApp t1 (TyVar v)) = v : freeAtomsVars t1
freeAtomsVars (TyApp t1 _) = freeAtomsVars t1
freeAtomsVars t = []

----------------------------------------------------------------------
-- Types and coeffects are terms

instance Term Type where
    freeVars = runIdentity . typeFoldM TypeFold
      { tfFunTy   = \_ x y -> return $ x <> y
      , tfTyCon   = \_ -> return [] -- or: const (return [])
      , tfBox     = \c t -> return $ freeVars c <> t
      , tfDiamond = \e t -> return $ e <> t
      , tfTyVar   = \v -> return [v] -- or: return . return
      , tfTyApp   = \x y -> return $ x <> y
      , tfTyInt   = \_ -> return []
      , tfTyInfix = \_ y z -> return $ y <> z
      , tfSet     = return . concat
      , tfTySig   = \t _ _ -> return t
      , tfTyFloat = \_ -> return []
      }

    isLexicallyAtomic TyInt{} = True
    isLexicallyAtomic TyFloat{} = True
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
        binds' <- mapM (\(v, k) -> do { v' <- freshIdentifierBase Type v;
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
        v' <- lookupVar Type v
        case v' of
           Just v' -> return (TyVar $ Id (sourceName v) v')
           -- This case happens if we are referring to a defined
           -- function which does not get its name freshened
           Nothing -> return (TyVar $ mkId (sourceName v))

----------------------------------------------------------------------

level :: Type
level = TyCon (mkId "Level")

-- | Normalise a coeffect using the semiring laws and some
--   local evaluation of natural numbers
--   There is plenty more scope to make this more comprehensive
--   None of this is stricly necessary but it improves type errors
--   and speeds up some constarint solving.
normalise :: Type -> Type
normalise (TyInfix TyOpPlus (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `max` m)
normalise (TyInfix TyOpTimes (TyApp (TyCon (internalName -> "Level")) n) (TyApp (TyCon (internalName -> "Level")) m)) = TyApp (TyCon (mkId "Level")) (n `min` m)
normalise (TyInfix TyOpPlus (TyFloat n) (TyFloat m)) = TyFloat (n + m)
normalise (TyInfix TyOpTimes (TyFloat n) (TyFloat m)) = TyFloat (n * m)
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
