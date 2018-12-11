{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

-- Syntax of types, coeffects, and effects

module Language.Granule.Syntax.Type where

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

import GHC.Generics (Generic)
import Data.Functor.Identity (runIdentity)

-- | Represent types with a universal quantification at the start
data TypeScheme =
  Forall
    Span          -- span of the scheme
    [(Id, Kind)]  -- binders
    Type          -- type
  deriving (Eq, Show, Generic)

-- Constructors and operators are just strings
type Operator = String

{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy Type Type           -- ^ Function type
          | TyCon Id                  -- ^ Type constructor
          | Box Coeffect Type         -- ^ Coeffect type
          | Diamond Effect Type       -- ^ Effect type
          | TyVar Id                  -- ^ Type variable
          | TyApp Type Type           -- ^ Type application
          | TyInt Int                 -- ^ Type-level Int
          | TyInfix Operator Type Type  -- ^ Infix type operator
    deriving (Eq, Ord, Show)

-- | Kinds
data Kind = KType
          | KCoeffect
          | KFun Kind Kind
          | KVar Id              -- Kind poly variable
          | KPromote Type        -- Promoted types
    deriving (Show, Ord, Eq)

kConstr = KPromote . TyCon

-- | Represents coeffect grades
data Coeffect = CNat      Int
              | CFloat    Rational
              | CInfinity (Maybe Type)
              | CInterval { lowerBound :: Coeffect, upperBound :: Coeffect }
              | CVar      Id
              | CPlus     Coeffect Coeffect
              | CTimes    Coeffect Coeffect
              | CMeet     Coeffect Coeffect
              | CJoin     Coeffect Coeffect
              | CZero     Type
              | COne      Type
              | Level     Int
              | CSet      [(String, Type)]
              | CSig      Coeffect Type
              | CExpon    Coeffect Coeffect
    deriving (Eq, Ord, Show)

nat = TyCon $ mkId "Nat"
extendedNat = TyApp (TyCon $ mkId "Ext") (TyCon $ mkId "Nat")
infinity = CInfinity (Just extendedNat)

isInterval :: Type -> Maybe Type
isInterval (TyApp (TyCon c) t) | internalName c == "Interval" = Just t
isInterval _ = Nothing

-- | Represents effect grades
-- TODO: Make richer
type Effect = [String]

----------------------------------------------------------------------
-- Helpers

-- | Natural numbers
type Nat = Word

-- | Compute the arity of a function type
arity :: Type -> Nat
arity (FunTy _ t) = 1 + arity t
arity _           = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type -> Type
resultType (FunTy _ t) = resultType t
resultType t = t

-- | Smart constructor for type constructors
con :: String -> Type
con = TyCon . mkId

-- | Smart constructor for type variables
var :: String -> Type
var = TyVar . mkId

-- | Smart constructor for function types
(.->) :: Type -> Type -> Type
s .-> t = FunTy s t

-- | Smart constructor for type application
(.@) :: Type -> Type -> Type
s .@ t = TyApp s t

-- Trivially effectful monadic constructors
mFunTy :: Monad m => Type -> Type -> m Type
mFunTy x y   = return (FunTy x y)
mTyCon :: Monad m => Id -> m Type
mTyCon       = return . TyCon
mBox :: Monad m => Coeffect -> Type -> m Type
mBox c y     = return (Box c y)
mDiamond :: Monad m => Effect -> Type -> m Type
mDiamond e y = return (Diamond e y)
mTyVar :: Monad m => Id -> m Type
mTyVar       = return . TyVar
mTyApp :: Monad m => Type -> Type -> m Type
mTyApp x y   = return (TyApp x y)
mTyInt :: Monad m => Int -> m Type
mTyInt       = return . TyInt
mTyInfix :: Monad m => Operator -> Type -> Type -> m Type
mTyInfix op x y  = return (TyInfix op x y)

-- Monadic algebra for types
data TypeFold m a = TypeFold
  { tfFunTy   :: a -> a        -> m a
  , tfTyCon   :: Id            -> m a
  , tfBox     :: Coeffect -> a -> m a
  , tfDiamond :: Effect -> a   -> m a
  , tfTyVar   :: Id            -> m a
  , tfTyApp   :: a -> a        -> m a
  , tfTyInt   :: Int           -> m a
  , tfTyInfix :: Operator -> a -> a -> m a }

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type
baseTypeFold =
  TypeFold mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix

-- | Monadic fold on a `Type` value
typeFoldM :: Monad m => TypeFold m a -> Type -> m a
typeFoldM algebra = go
  where
   go (FunTy t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy algebra) t1' t2'
   go (TyCon s) = (tfTyCon algebra) s
   go (Box c t) = do
     t' <- go t
     (tfBox algebra) c t'
   go (Diamond c t) = do
     t' <- go t
     (tfDiamond algebra) c t'
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

instance FirstParameter TypeScheme Span

----------------------------------------------------------------------
-- Types and coeffects are terms

instance Term Type where
  freeVars = runIdentity . typeFoldM TypeFold
    { tfFunTy   = \x y -> return $ x <> y
    , tfTyCon   = \_ -> return [] -- or: const (return [])
    , tfBox     = \c t -> return $ freeVars c <> t
    , tfDiamond = \_ x -> return x
    , tfTyVar   = \v -> return [v] -- or: return . return
    , tfTyApp   = \x y -> return $ x <> y
    , tfTyInt   = \_ -> return []
    , tfTyInfix = \_ y z -> return $ y <> z
    }

instance Term Coeffect where
    freeVars (CVar v) = [v]
    freeVars (CPlus c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CTimes c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CExpon c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CMeet c1 c2) = freeVars c1 <> freeVars c2
    freeVars (CJoin c1 c2) = freeVars c1 <> freeVars c2
    freeVars CNat{}  = []
    freeVars CFloat{} = []
    freeVars CInfinity{} = []
    freeVars CZero{} = []
    freeVars COne{} = []
    freeVars Level{} = []
    freeVars CSet{} = []
    freeVars (CSig c _) = freeVars c
    freeVars (CInterval c1 c2) = freeVars c1 <> freeVars c2

----------------------------------------------------------------------
-- Freshenable instances

instance Freshenable TypeScheme where
  freshen :: TypeScheme -> Freshener TypeScheme
  freshen (Forall s binds ty) = do
        binds' <- mapM (\(v, k) -> do { v' <- freshVar Type v; return (v', k) }) binds
        ty' <- freshen ty
        return $ Forall s binds' ty'

instance Freshenable Type where
  freshen =
    typeFoldM (baseTypeFold { tfTyApp = rewriteTyApp,
                              tfTyVar = freshenTyVar,
                              tfBox = freshenTyBox })
    where
      -- Rewrite type aliases of Box
      rewriteTyApp t1@(TyCon ident) t2
        | internalName ident == "Box" || internalName ident == "◻" =
          return $ Box (CInterval (CZero extendedNat) infinity) t2
      rewriteTyApp t1 t2 = return $ TyApp t1 t2

      freshenTyBox c t = do
        c' <- freshen c
        t' <- freshen t
        return $ Box c' t'
      freshenTyVar v = do
        v' <- lookupVar Type v
        case v' of
           Just v' -> return (TyVar $ Id (sourceName v) v')
           -- This case happens if we are referring to a defined
           -- function which does not get its name freshened
           Nothing -> return (TyVar $ mkId (sourceName v))

instance Freshenable Coeffect where
    freshen (CVar v) = do
      v' <- lookupVar Type v
      case v' of
        Just v' -> return $ CVar $ Id (sourceName v) v'
        Nothing -> return $ CVar $ mkId (sourceName v)

    freshen (CInfinity (Just (TyVar i@(Id _ "")))) = do
      t <- freshVar Type i
      return $ CInfinity $ Just $ TyVar t

    freshen (CPlus c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CPlus c1' c2'

    freshen (CTimes c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CTimes c1' c2'

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
      return $ CSig c' k
    freshen c@CInfinity{} = return c
    freshen c@CFloat{} = return c
    freshen c@CZero{}  = return c
    freshen c@COne{}   = return c
    freshen c@Level{}  = return c
    freshen c@CNat{}   = return c
    freshen (CInterval c1 c2) = CInterval <$> freshen c1 <*> freshen c2

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
normalise (CSig (CNat 0) k) = CZero k
normalise (CSig (CZero _)  k) = CZero k
normalise (CSig (CNat 1) k) = COne k
normalise (CSig (COne _)   k) = CZero k
normalise (CSig (CInfinity _)  k) = CInfinity (Just k)

normalise c = c
