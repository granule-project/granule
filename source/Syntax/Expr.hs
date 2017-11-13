{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax.Expr (Id, Value(..), Expr(..), Type(..), TypeScheme(..),
                   Def(..), Op(..),
                   Pattern(..), CKind(..), Coeffect(..), NatModifier(..), Effect,
                   uniqueNames, arity, freeVars, subst,
                   normalise,
                   nullSpan, getSpan, getEnd, getStart, Pos, Span,
                   freshenBlankPolyVars
                   ) where

import Data.List ((\\))
import Control.Monad.State
import GHC.Generics (Generic)

import Syntax.FirstParameter

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

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
           | Constr String [Value]
           | Pair Expr Expr
          deriving (Eq, Show)

-- Expressions (computations) in Granule
data Expr = App Span Expr Expr
          | Binop Span Op Expr Expr
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
             | PConstr Span String  -- Constructor pattern
             | PApp Span Pattern Pattern -- Apply pattern
             | PPair Span Pattern Pattern -- ^ Pair patterns
          deriving (Eq, Show, Generic)

instance FirstParameter Pattern Span

class Binder t where
  bvs :: t -> [Id]
  freshenBinder :: t -> Freshener t

instance Binder Pattern where
  bvs (PVar _ v)     = [v]
  bvs (PBox _ p)     = bvs p
  bvs (PApp _ p1 p2) = bvs p1 ++ bvs p2
  bvs _           = [] -- TODO: Get rid of catch-alls

  freshenBinder (PVar s var) = do
      var' <- freshVar var
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

type Freshener t = State (Int, [(Id, Id)]) t

class Term t where
  -- Compute the free variables in a term
  freeVars :: t -> [Id]
  -- Syntactic substitution of an expression into a term
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr -> Id -> t -> Expr
  -- Freshen
  freshen :: t -> Freshener t

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshVar :: Id -> Freshener Id
freshVar var = do
   (v, nmap) <- get
   let var' = var ++ show v
   put (v+1, (var, var') : nmap)
   return var'

freshenBlankPolyVars :: [Def] -> [Def]
freshenBlankPolyVars defs =
    evalState (mapM freshenDef defs) (0 :: Int, [])
  where
    freshenDef (Def s identifier expr pats tys) = do
      tys' <- freshenTys tys
      return $ Def s identifier expr pats tys'

    freshenTys (Forall s binds ty) = do
      ty' <- freshenTy ty
      return $ Forall s binds ty'

    freshenTy (FunTy t1 t2) = do
      t1' <- freshenTy t1
      t2' <- freshenTy t2
      return $ FunTy t1' t2'
    freshenTy (Box c t)     = do
      c' <- freshenCoeff c
      t' <- freshenTy t
      return $ Box c' t'
    freshenTy (Diamond e t) = do
      t' <- freshenTy t
      return $ Diamond e t'
    freshenTy t = return t

    freshenCoeff (CStar (CPoly "")) = do
      t <- freshVar "d"
      return $ CStar (CPoly t)
    freshenCoeff (CStar (CPoly " star")) = do
      t <- freshVar " star"
      return $ CStar (CPoly t)
    freshenCoeff (CPlus c1 c2) = do
      c1' <- freshenCoeff c1
      c2' <- freshenCoeff c2
      return $ CPlus c1' c2'
    freshenCoeff (CTimes c1 c2) = do
      c1' <- freshenCoeff c1
      c2' <- freshenCoeff c2
      return $ CTimes c1' c2'
    freshenCoeff (CSet cs) = do
      cs' <- mapM (\(s, t) -> freshenTy t >>= (\t' -> return (s, t'))) cs
      return $ CSet cs'
    freshenCoeff (CSig c k) = do
      c' <- freshenCoeff c
      return $ CSig c' k
    freshenCoeff c = return c

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
      var' <- freshVar var
      e'   <- freshen e
      return $ Abs var' t e'

    freshen (Pure e) = do
      e' <- freshen e
      return $ Pure e'

    freshen (Promote e) = do
      e' <- freshen e
      return $ Promote e'

    freshen (Var v) = do
      (_, nmap) <- get
      case lookup v nmap of
         Just v' -> return (Var v')
         -- This case happens if we are referring to a defined
         -- function which does not get its name freshened
         Nothing -> return (Var v)

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
                                      \\ concatMap (bvs . fst) cases)

    subst es v (App s e1 e2)        = App s (subst es v e1) (subst es v e2)
    subst es v (Binop s op e1 e2)   = Binop s op (subst es v e1) (subst es v e2)
    subst es v (LetBox s w t e1 e2) = LetBox s w t (subst es v e1) (subst es v e2)
    subst es v (LetDiamond s w t e1 e2) =
                                   LetDiamond s w t (subst es v e1) (subst es v e2)
    subst es v (Val _ val)          = subst es v val
    subst es v (Case s expr cases)  = Case s
                                     (subst es v expr)
                                     (map (\(p, e) -> (p, subst es v e)) cases)

    freshen (LetBox s var t e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen e2
      return $ LetBox s var' t e1' e2'

    freshen (App s e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ App s e1' e2'

    freshen (LetDiamond s var t e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen e2
      return $ LetDiamond s var' t e1' e2'

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
          deriving (Eq, Show, Generic)

instance FirstParameter Def Span

-- Alpha-convert all bound variables
uniqueNames :: [Def] -> ([Def], [(Id, Id)])
uniqueNames = (\(defs, (_, nmap)) -> (defs, nmap))
            . flip runState (0 :: Int, [])
            . mapM freshenDef
  where
    freshenDef (Def s var e ps t) = do
      ps' <- mapM freshenBinder ps
      e'  <- freshen e
      return $ Def s var e' ps' t

----------- Types

data TypeScheme = Forall Span [(String, CKind)] Type
    deriving (Eq, Show, Generic)

instance FirstParameter TypeScheme Span

{-| Types.
Example: `List n Int` is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy Type Type           -- ^ Function type
          | TyCon String              -- ^ Type constructor
          | Box Coeffect Type         -- ^ Coeffect type
          | Diamond Effect Type       -- ^ Effect type
          | TyVar String              -- ^ Type variable
          | TyApp Type Type           -- ^ Type application
          | TyInt Int                 -- ^ Type-level Int
          | PairTy Type Type          -- ^ Pair/product type
    deriving (Eq, Ord, Show)

arity :: Type -> Int
arity (FunTy _ t) = 1 + arity t
arity _           = 0

type Effect = [String]

data Coeffect = CNat   NatModifier Int
              | CNatOmega (Either () Int)
              | CFloat  Rational
              | CStar  CKind
              | CVar   String
              | CPlus  Coeffect Coeffect
              | CTimes Coeffect Coeffect
              | CZero  CKind
              | COne   CKind
              | Level Int
              | CSet [(String, Type)]
              | CSig Coeffect CKind
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
normalise (COne (CConstr "Nat")) = CNat Ordered 1
normalise (CZero (CConstr "Nat")) = CNat Ordered 0
normalise (COne (CConstr "Nat=")) = CNat Discrete 1
normalise (CZero (CConstr "Nat=")) = CNat Discrete 0
normalise (COne (CConstr "Level")) = Level 1
normalise (CZero (CConstr "Level")) = Level 0
normalise (COne (CConstr "Q")) = CFloat 1
normalise (CZero (CConstr "Q")) = CFloat 0
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
normalise (CSig (CStar _)  k) = CStar k
normalise c = c
