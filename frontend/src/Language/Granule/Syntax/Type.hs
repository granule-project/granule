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

import Data.Functor.Identity (runIdentity)
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
  deriving (Eq, Ord, Show, Rp.Data)


{-| Types.
Example: `List n Int` in Granule
         is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy (Maybe Id) Type Type      -- ^ Function type
          | TyCon Id                        -- ^ Type constructor
          | Box Coeffect Type               -- ^ Coeffect type
          | Diamond Type Type               -- ^ Effect type
          | TyVar Id                        -- ^ Type variable
          | TyApp Type Type                 -- ^ Type application
          | TyInt Int                       -- ^ Type-level Int
          | TyInfix TypeOperator Type Type  -- ^ Infix type operator
          | TySet [Type]                    -- ^ Type-level set
          | TySig Type Kind                 -- ^ Signature
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

-- | Represents coeffect grades
data Coeffect = CNat      Int
              | CFloat    Rational
              | CInfinity (Maybe Type)
              | CInterval { lowerBound :: Coeffect, upperBound :: Coeffect }
              | CVar      Id
              | CPlus     Coeffect Coeffect
              | CTimes    Coeffect Coeffect
              | CMinus    Coeffect Coeffect
              | CMeet     Coeffect Coeffect
              | CJoin     Coeffect Coeffect
              | CZero     Type
              | COne      Type
              | Level     Integer
              | CSet      [(String, Type)]
              | CSig      Coeffect Type
              | CExpon    Coeffect Coeffect
              | CProduct  Coeffect Coeffect
    deriving (Eq, Ord, Show, Rp.Data)

-- Algebra for coeffects
data CoeffectFold a = CoeffectFold
  { cNat   :: Int -> a
  , cFloat :: Rational -> a
  , cInf   :: Maybe Type -> a
  , cInterval :: a -> a -> a
  , cVar   :: Id -> a
  , cPlus  :: a -> a -> a
  , cTimes :: a -> a -> a
  , cMinus :: a -> a -> a
  , cMeet  :: a -> a -> a
  , cJoin  :: a -> a -> a
  , cZero  :: Type -> a
  , cOne   :: Type -> a
  , cLevel :: Integer -> a
  , cSet   :: [(String, Type)] -> a
  , cSig   :: a -> Type -> a
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

nat, extendedNat :: Type
nat = TyCon $ mkId "Nat"
extendedNat = TyApp (TyCon $ mkId "Ext") (TyCon $ mkId "Nat")

infinity :: Coeffect
infinity = CInfinity (Just extendedNat)

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
mBox :: Monad m => Coeffect -> Type -> m Type
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

-- Monadic algebra for types
data TypeFold m a = TypeFold
  { tfFunTy   :: Maybe Id -> a -> a     -> m a
  , tfTyCon   :: Id                     -> m a
  , tfBox     :: Coeffect -> a          -> m a
  , tfDiamond :: a -> a                 -> m a
  , tfTyVar   :: Id                     -> m a
  , tfTyApp   :: a -> a                 -> m a
  , tfTyInt   :: Int                    -> m a
  , tfTyInfix :: TypeOperator -> a -> a -> m a
  , tfSet     :: [a]                    -> m a
  , tfTySig   :: a -> Type -> Kind      -> m a  }

-- Base monadic algebra
baseTypeFold :: Monad m => TypeFold m Type
baseTypeFold =
  TypeFold mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix mTySet mTySig

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
        binds' <- mapM (\(v, k) -> do { v' <- freshIdentifierBase Type v;
                                        k' <- freshen k;
                                        return (v', k') }) binds
        constraints' <- mapM freshen constraints
        ty' <- freshen ty
        return $ Forall s binds' constraints' ty'

instance Freshenable m Type where
  freshen =
    typeFoldM (baseTypeFold { tfTyVar = freshenTyVar,
                              tfBox = freshenTyBox })
    where

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

instance Freshenable m Coeffect where
    freshen (CVar v) = do
      v' <- lookupVar Type v
      case v' of
        Just v' -> return $ CVar $ Id (sourceName v) v'
        Nothing -> return $ CVar v

    freshen (CInfinity (Just (TyVar i@(Id _ "")))) = do
      t <- freshIdentifierBase Type i
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
