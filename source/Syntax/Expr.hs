{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax.Expr (Value(..), Expr(..), Type(..), TypeScheme(..),
                   Def(..), Pattern(..), CKind(..), Coeffect(..),
                   NatModifier(..), Effect, Kind(..), DataConstr(..), TypeConstr(..),
                   Id, sourceName, internalName, mkId, mkInternalId,
                   Operator,
                   liftCoeffectType,
                   uniqueNames, arity, freeVars, subst,
                   normalise,
                   nullSpan, getSpan, getEnd, getStart, Pos, Span,
                   typeFoldM, TypeFold(..),
                   mFunTy, mTyCon, mBox, mDiamond, mTyVar, mTyApp,
                   mTyInt, mPairTy, mTyInfix,
                   baseTypeFold
                   ) where

import Data.List ((\\))
import Control.Monad.State
import Control.Arrow
import GHC.Generics (Generic)
import Data.Functor.Identity (runIdentity)

import Syntax.FirstParameter

-- Internal representation of names (variables)
-- which pairs their source name string with an internal name
-- which is useually freshly generate. Error messages should
-- always use the 'sourceName', anything involving new name
-- generation should use 'internalName'
data Id = Id { sourceName :: String, internalName :: String }
  deriving (Eq, Ord)

instance Show Id where
  show (Id s i) = "Id " ++ show s ++ " " ++ show i

-- Constructors and operators are just strings
type Operator      = String

mkId :: String -> Id
mkId x = Id x x

mkInternalId :: String -> String -> Id
mkInternalId = Id

type Pos = (Int, Int) -- (line, column)
type Span = (Pos, Pos)
nullSpan :: Span
nullSpan = ((0, 0), (0, 0))

getSpan :: FirstParameter t Span => t -> Span
getSpan = getFirstParameter

getEnd ::  FirstParameter t Span => t -> Pos
getEnd = snd . getSpan

getStart ::  FirstParameter t Span => t -> Pos
getStart = fst . getSpan

-- Values in Granule
data Value = Abs Id (Maybe Type) Expr
           | NumInt Int
           | NumFloat Double
           | Promote Expr
           | Pure Expr
           | Var Id
           | Constr Id [Value]
           | Pair Expr Expr
          deriving (Eq, Show)

-- Expressions (computations) in Granule
data Expr = App Span Expr Expr
          | Binop Span Operator Expr Expr
          | LetBox Span Id Type Expr Expr
          | LetDiamond Span Id Type Expr Expr
          | Val Span Value
          | Case Span Expr [(Pattern, Expr)]
          deriving (Eq, Show, Generic)

instance FirstParameter Expr Span

-- Pattern matchings
data Pattern = PVar Span Id         -- Variable patterns
             | PWild Span           -- Wildcard (underscore) pattern
             | PBox Span Pattern -- Box patterns
             | PInt Span Int        -- Numeric patterns
             | PFloat Span Double
             | PConstr Span Id  -- Constructor pattern
             | PApp Span Pattern Pattern -- Apply pattern
             | PPair Span Pattern Pattern -- ^ Pair patterns
          deriving (Eq, Show, Generic)

instance FirstParameter Pattern Span

class Binder t where
  boundVars :: t -> [Id]
  freshenBinder :: t -> Freshener t

instance Binder Pattern where
  boundVars (PVar _ v)     = [v]
  boundVars PWild {}       = []
  boundVars (PBox _ p)     = boundVars p
  boundVars PInt {}        = []
  boundVars PFloat {}      = []
  boundVars PConstr {}     = []
  boundVars (PApp _ p1 p2) = boundVars p1 ++ boundVars p2
  boundVars (PPair _ p1 p2) = boundVars p1 ++ boundVars p2

  freshenBinder (PVar s var) = do
      var' <- freshVar Value var
      return $ PVar s var'

  freshenBinder (PBox s p) = do
      p' <- freshenBinder p
      return $ PBox s p'

  freshenBinder (PApp s p1 p2) = do
      p1' <- freshenBinder p1
      p2' <- freshenBinder p2
      return $ PApp s p1' p2'

  freshenBinder (PPair s p1 p2) = do
      p1' <- freshenBinder p1
      p2' <- freshenBinder p2
      return $ PPair s p1' p2'

  freshenBinder p = return p -- TODO: Get rid of catch-alls

type Freshener t = State (Int, [(String, String)], [(String, String)]) t

class Term t where
  -- Compute the free variables in a term
  freeVars :: t -> [Id]
  -- Syntactic substitution of a term into an expression
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr -> Id -> t -> Expr
  -- Freshen
  freshen :: t -> Freshener t

-- Used to distinguish the value-level and type-level variables
data IdSyntacticCategory = Value | Type

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshVar :: IdSyntacticCategory -> Id -> Freshener Id
freshVar synCat var = do
   (v, vmap, tmap) <- get
   let var' = sourceName var ++ show v
   case synCat of
       Value -> put (v+1, (sourceName var, var') : vmap, tmap)
       Type  -> put (v+1, vmap, (sourceName var, var') : tmap)
   return $ var { internalName = var' }

lookupVar :: IdSyntacticCategory -> Id -> Freshener (Maybe String)
lookupVar synCat var = do
  (_, vmap, tmap) <- get
  return $ case synCat of
    Value -> lookup (sourceName var) vmap
    Type  -> lookup (sourceName var) tmap

freshenTys :: TypeScheme -> Freshener TypeScheme
freshenTys (Forall s binds ty) = do
      binds' <- mapM (\(v, k) -> do { v' <- freshVar Type v; return (v', k) }) binds
      ty' <- freshen ty
      return $ Forall s binds' ty'

instance Term Type where
  freeVars = runIdentity . typeFoldM TypeFold
    { tfFunTy   = \x y -> return $ x ++ y
    , tfTyCon   = \_ -> return [] -- or: const (return [])
    , tfBox     = \c t -> return $ freeVars c ++ t
    , tfDiamond = \_ x -> return x
    , tfTyVar   = \v -> return [v] -- or: return . return
    , tfTyApp   = \x y -> return $ x ++ y
    , tfTyInt   = \_ -> return []
    , tfPairTy  = \x y -> return $ x ++ y
    , tfTyInfix = \_ y z -> return $ y ++ z
    }

  subst e _ t = e
  freshen =
    typeFoldM (baseTypeFold { tfTyVar = freshenTyVar, tfBox = freshenTyBox })
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

instance Term Coeffect where
    freeVars (CVar v) = [v]
    freeVars (CPlus c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CTimes c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CMeet c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CJoin c1 c2) = freeVars c1 ++ freeVars c2
    freeVars CNat{}  = []
    freeVars CNatOmega{} = []
    freeVars CFloat{} = []
    freeVars CInfinity{} = []
    freeVars CZero{} = []
    freeVars COne{} = []
    freeVars Level{} = []
    freeVars CSet{} = []
    freeVars (CSig c _) = freeVars c

    subst e _ _ = e

    freshen (CVar v) = do
      v' <- lookupVar Type v
      case v' of
        Just v' -> return $ CVar $ Id (sourceName v) v'
        Nothing -> return $ CVar $ mkId (sourceName v)
    freshen (CInfinity (CPoly i@(Id _ ""))) = do
      t <- freshVar Type i
      return $ CInfinity (CPoly t)
    freshen (CInfinity (CPoly i@(Id _ " infinity"))) = do
      t <- freshVar Type i
      return $ CInfinity (CPoly t)

    freshen (CPlus c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CPlus c1' c2'
    freshen (CTimes c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CTimes c1' c2'

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
    freshen c@CNatOmega{} = return c


instance Term Value where
    freeVars (Abs x _ e) = freeVars e \\ [x]
    freeVars (Var x)     = [x]
    freeVars (Pure e)    = freeVars e
    freeVars (Promote e) = freeVars e
    freeVars (Pair l r)  = freeVars l ++ freeVars r
    freeVars (NumInt _) = []
    freeVars (NumFloat _) = []
    freeVars (Constr _ _) = []

    subst es v (Abs w t e)      = Val nullSpan $ Abs w t (subst es v e)
    subst es v (Pure e)         = Val nullSpan $ Pure (subst es v e)
    subst es v (Promote e)      = Val nullSpan $ Promote (subst es v e)
    subst es v (Pair l r)       = Val nullSpan $ Pair (subst es v l) (subst es v r)
    subst es v (Var w) | v == w = es
    subst _ _ v@(NumInt _)        = Val nullSpan v
    subst _ _ v@(NumFloat _)      = Val nullSpan v
    subst _ _ v@(Var _)           = Val nullSpan v
    subst _ _ v@(Constr _ _)      = Val nullSpan v

    freshen (Abs var t e) = do
      var' <- freshVar Value var
      e'   <- freshen e
      return $ Abs var' t e'

    freshen (Pure e) = do
      e' <- freshen e
      return $ Pure e'

    freshen (Promote e) = do
      e' <- freshen e
      return $ Promote e'

    freshen (Var v) = do
      v' <- lookupVar Value v
      case v' of
         Just v' -> return (Var $ Id (sourceName v) v')
         -- This case happens if we are referring to a defined
         -- function which does not get its name freshened
         Nothing -> return (Var $ Id (sourceName v) (sourceName v))

    freshen (Pair l r) = do
      l' <- freshen l
      r' <- freshen r
      return $ Pair l' r'

    freshen v@(NumInt _)   = return v
    freshen v@(NumFloat _) = return v
    freshen v@(Constr _ _) = return v

instance Term Expr where
    freeVars (App _ e1 e2)            = freeVars e1 ++ freeVars e2
    freeVars (Binop _ _ e1 e2)        = freeVars e1 ++ freeVars e2
    freeVars (LetBox _ x _ e1 e2)     = freeVars e1 ++ (freeVars e2 \\ [x])
    freeVars (LetDiamond _ x _ e1 e2) = freeVars e1 ++ (freeVars e2 \\ [x])
    freeVars (Val _ e)                = freeVars e
    freeVars (Case _ e cases)         = freeVars e ++ (concatMap (freeVars . snd) cases
                                      \\ concatMap (boundVars . fst) cases)

    subst es v (App s e1 e2)        = App s (subst es v e1) (subst es v e2)
    subst es v (Binop s op e1 e2)   = Binop s op (subst es v e1) (subst es v e2)
    subst es v (LetBox s w t e1 e2) = LetBox s w t (subst es v e1) (subst es v e2)
    subst es v (LetDiamond s w t e1 e2) =
                                   LetDiamond s w t (subst es v e1) (subst es v e2)
    subst es v (Val _ val)          = subst es v val
    subst es v (Case s expr cases)  = Case s
                                     (subst es v expr)
                                     (map (second (subst es v)) cases)

    freshen (LetBox s var t e1 e2) = do
      var' <- freshVar Value var
      e1'  <- freshen e1
      e2'  <- freshen e2
      t'   <- freshen t
      return $ LetBox s var' t' e1' e2'

    freshen (App s e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ App s e1' e2'

    freshen (LetDiamond s var t e1 e2) = do
      var' <- freshVar Value var
      e1'  <- freshen e1
      e2'  <- freshen e2
      t'   <- freshen t
      return $ LetDiamond s var' t' e1' e2'

    freshen (Binop s op e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ Binop s op e1' e2'

    freshen (Case s expr cases) = do
      expr'     <- freshen expr
      cases' <- forM cases $ \(p, e) -> do
                  p' <- freshenBinder p
                  e' <- freshen e
                  return (p', e')
      return (Case s expr' cases')

    freshen (Val s v) = do
     v' <- freshen v
     return (Val s v')

--------- Definitions

data Def = Def Span Id Expr [Pattern] TypeScheme
         | ADT Span TypeConstr [TyVar] [DataConstr]
          deriving (Eq, Show, Generic)

type TyVar = (Span,Id)

instance FirstParameter Def Span

data TypeConstr = TypeConstr Span Id deriving (Eq, Show, Generic)

instance FirstParameter TypeConstr Span

data DataConstr = DataConstr Span Id TypeScheme deriving (Eq, Show, Generic)

instance FirstParameter DataConstr Span

-- Alpha-convert all bound variables
uniqueNames :: [Def] -> ([Def], Int)
uniqueNames =
   -- Since the type checker will generate new fresh names as well
   -- find the maximum fresh id that occured in the renaming stage
   -- so that there will be no clashes later
   foldr (\def (freshDefs, maxFresh) ->
      let (def', (maxFresh', _, _)) = runState (freshenDef def) (0 :: Int, [], [])
      in (def' : freshDefs, maxFresh `max` maxFresh')) ([], 0)
  where
    freshenDef (Def s var e ps t) = do
      ps' <- mapM freshenBinder ps
      t'  <- freshenTys t
      e'  <- freshen e
      return $ Def s var e' ps' t'

    freshenDef a@(ADT _ _ _ _) = return a

----------- Types

data TypeScheme = Forall Span [(Id, Kind)] Type -- [(Id, Kind)] are the binders
    deriving (Eq, Show, Generic)

instance FirstParameter TypeScheme Span

{-| Types.
Example: `List n Int` is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy Type Type           -- ^ Function type
          | TyCon Id       -- ^ Type constructor
          | Box Coeffect Type         -- ^ Coeffect type
          | Diamond Effect Type       -- ^ Effect type
          | TyVar Id                  -- ^ Type variable
          | TyApp Type Type           -- ^ Type application
          | TyInt Int                 -- ^ Type-level Int
          | PairTy Type Type          -- ^ Pair/product type
          | TyInfix Operator Type Type  -- ^ Infix type operator
    deriving (Eq, Ord, Show)

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
mPairTy :: Monad m => Type -> Type -> m Type
mPairTy x y  = return (PairTy x y)
mTyInfix :: Monad m => Operator -> Type -> Type -> m Type
mTyInfix op x y  = return (TyInfix op x y)

baseTypeFold :: Monad m => TypeFold m Type
baseTypeFold =
  TypeFold mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mPairTy mTyInfix

data TypeFold m a = TypeFold
  { tfFunTy   :: a -> a        -> m a
  , tfTyCon   :: Id -> m a
  , tfBox     :: Coeffect -> a -> m a
  , tfDiamond :: Effect -> a   -> m a
  , tfTyVar   :: Id            -> m a
  , tfTyApp   :: a -> a        -> m a
  , tfTyInt   :: Int           -> m a
  , tfPairTy  :: a -> a        -> m a
  , tfTyInfix :: Operator -> a -> a -> m a }

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
   go (PairTy t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfPairTy algebra) t1' t2'
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfix algebra) op t1' t2'

arity :: Type -> Int
arity (FunTy _ t) = 1 + arity t
arity _           = 0

data Kind = KType
          | KCoeffect
          | KFun Kind Kind
          | KPoly Id              -- Kind poly variable
          | KConstr Id -- constructors that have been elevated
    deriving (Show, Ord, Eq)

liftCoeffectType :: CKind -> Kind
liftCoeffectType (CConstr cid) = KConstr cid
liftCoeffectType (CPoly var)   = KPoly var

type Effect = [String]

data Coeffect = CNat      NatModifier Int
              | CNatOmega (Either () Int)
              | CFloat    Rational
              | CInfinity CKind
              | CVar      Id
              | CPlus     Coeffect Coeffect
              | CTimes    Coeffect Coeffect
              | CMeet     Coeffect Coeffect
              | CJoin     Coeffect Coeffect
              | CZero     CKind
              | COne      CKind
              | Level     Int
              | CSet      [(String, Type)]
              | CSig      Coeffect CKind
    deriving (Eq, Ord, Show)

data NatModifier = Ordered | Discrete
    deriving (Show, Ord, Eq)

data CKind = CConstr Id | CPoly Id
    deriving (Eq, Ord, Show)

-- | Normalise a coeffect using the semiring laws and some
--   local evaluation of natural numbers
--   There is plenty more scope to make this more comprehensive
normalise :: Coeffect -> Coeffect
normalise (CPlus (CZero _) n) = n
normalise (CPlus n (CZero _)) = n
normalise (CTimes (COne _) n) = n
normalise (CTimes n (COne _)) = n
normalise (COne (CConstr (Id _ "Nat"))) = CNat Ordered 1
normalise (CZero (CConstr (Id _ "Nat"))) = CNat Ordered 0
normalise (COne (CConstr (Id _ "Nat="))) = CNat Discrete 1
normalise (CZero (CConstr (Id _ "Nat="))) = CNat Discrete 0
normalise (COne (CConstr (Id _ "Level"))) = Level 1
normalise (CZero (CConstr (Id _ "Level"))) = Level 0
normalise (COne (CConstr (Id _ "Q"))) = CFloat 1
normalise (CZero (CConstr (Id _ "Q"))) = CFloat 0
normalise (CPlus (Level n) (Level m)) = Level (n `max` m)
normalise (CTimes (Level n) (Level m)) = Level (n `min` m)
normalise (CPlus (CFloat n) (CFloat m)) = CFloat (n + m)
normalise (CTimes (CFloat n) (CFloat m)) = CFloat (n * m)
normalise (CPlus (CNat k n) (CNat k' m)) | k == k' = CNat k (n + m)
normalise (CTimes (CNat k n) (CNat k' m)) | k == k' = CNat k (n * m)
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
normalise (CSig (CNat _ 0) k) = CZero k
normalise (CSig (CZero _)  k) = CZero k
normalise (CSig (CNat _ 1) k) = COne k
normalise (CSig (COne _)   k) = CZero k
normalise (CSig (CInfinity _)  k) = CInfinity k
normalise c = c
