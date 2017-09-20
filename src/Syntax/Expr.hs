{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax.Expr (Id, Value(..), Expr(..), Type(..), TypeScheme(..),
                   Def(..), Op(..),
                   Pattern(..), CKind(..), Coeffect(..), NatModifier(..), Effect,
                   uniqueNames, arity, fvs, subst
                   ) where

import Data.List
import Control.Monad.State

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

-- Values in Granule
data Value = Abs Id (Maybe Type) Expr
           | NumInt Int
           | NumFloat Double
           | Promote Expr
           | Pure Expr
           | Var Id
           | Constr String
          deriving (Eq, Show)

-- Expressions (computations) in Granule
data Expr = App Expr Expr
          | Binop Op Expr Expr
          | LetBox Id Type CKind Expr Expr
          | LetDiamond Id Type Expr Expr
          | Val Value
          | Case Expr [(Pattern, Expr)]
          deriving (Eq, Show)

-- Pattern matchings
data Pattern = PVar Id        -- Variable patterns
             | PWild          -- Wildcard (underscore) pattern
             | PBoxVar Id     -- Box patterns (with a variable pattern inside)
             | PInt Int       -- Numeric patterns
             | PFloat Double
             | PConstr String -- Constructor pattern
             | PApp Pattern Pattern -- Apply pattern
          deriving (Eq, Show)

class Binder t where
  bvs :: t -> [Id]
  freshenBinder :: t -> Freshener t

instance Binder Pattern where
  bvs (PVar v)    = [v]
  bvs (PBoxVar v) = [v]
  bvs (PApp p1 p2) = bvs p1 ++ bvs p2
  bvs _           = []

  freshenBinder (PVar var) = do
      var' <- freshVar var
      return $ PVar var'

  freshenBinder (PBoxVar var) = do
      var' <- freshVar var
      return $ PBoxVar var'

  freshenBinder (PApp p1 p2) = do
      p1' <- freshenBinder p1
      p2' <- freshenBinder p2
      return $ PApp p1' p2'

  freshenBinder p = return p

type Freshener t = State (Int, [(Id, Id)]) t

class Term t where
  -- Compute the free variables in a term
  fvs :: t -> [Id]
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

instance Term Value where
    fvs (Abs x _ e) = (fvs e) \\ [x]
    fvs (Var x)     = [x]
    fvs (Pure e)    = fvs e
    fvs (Promote e) = fvs e
    fvs _           = []

    subst es v (Abs w t e)      = Val $ Abs w t (subst es v e)
    subst es v (Pure e)         = Val $ Pure (subst es v e)
    subst es v (Promote e)      = Val $ Promote (subst es v e)
    subst es v (Var w) | v == w = es
    subst _ _ val               = Val val

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

    freshen v = return v

instance Term Expr where
   fvs (App e1 e2)            = fvs e1 ++ fvs e2
   fvs (Binop _ e1 e2)        = fvs e1 ++ fvs e2
   fvs (LetBox x _ _ e1 e2)   = fvs e1 ++ ((fvs e2) \\ [x])
   fvs (LetDiamond x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
   fvs (Val e)                = fvs e
   fvs (Case e cases)         = fvs e ++ (concatMap (fvs . snd) cases
                                      \\ concatMap (bvs . fst) cases)

   subst es v (App e1 e2)        = App (subst es v e1) (subst es v e2)
   subst es v (Binop op e1 e2)   = Binop op (subst es v e1) (subst es v e2)
   subst es v (LetBox w t k e1 e2) = LetBox w t k (subst es v e1) (subst es v e2)
   subst es v (LetDiamond w t e1 e2) =
                                   LetDiamond w t (subst es v e1) (subst es v e2)
   subst es v (Val val)          = subst es v val
   subst es v (Case expr cases)  = Case
                                     (subst es v expr)
                                     (map (\(p, e) -> (p, subst es v e)) cases)

   freshen (LetBox var t k e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen e2
      return $ LetBox var' t k e1' e2'

   freshen (App e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ App e1' e2'

   freshen (LetDiamond var t e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen e2
      return $ LetDiamond var' t e1' e2'

   freshen (Binop op e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ Binop op e1' e2'

   freshen (Case expr cases) = do
      expr'     <- freshen expr
      cases' <- forM cases $ \(p, e) -> do
                  p' <- freshenBinder p
                  e' <- freshen e
                  return (p', e')
      return (Case expr' cases')

   freshen (Val v) = do
     v' <- freshen v
     return (Val v')


--------- Definitions

data Def = Def Id Expr [Pattern] TypeScheme
          deriving (Eq, Show)

-- Alpha-convert all bound variables
uniqueNames :: [Def] -> ([Def], [(Id, Id)])
uniqueNames = (\(defs, (_, nmap)) -> (defs, nmap))
            . flip runState (0 :: Int, [])
            . mapM freshenDef
  where
    freshenDef (Def var e ps t) = do
      e'  <- freshen e
      ps' <- mapM freshenBinder ps
      return $ Def var e' ps' t

----------- Types

data TypeScheme = Forall [(String, CKind)] Type
    deriving (Eq, Show)

data Type = FunTy Type Type
          | ConT String
          | Box Coeffect Type
          | Diamond Effect Type
          | TyVar String
    deriving (Eq, Ord, Show)

arity :: Type -> Int
arity (FunTy _ t) = 1 + arity t
arity _           = 0

type Effect = [String]

data Coeffect = CNat   NatModifier Int
              | CFloat  Rational
              | CNatOmega (Either () Int)
              | CVar   String
              | CPlus  Coeffect Coeffect
              | CTimes Coeffect Coeffect
              | CZero  CKind
              | COne   CKind
              | Level Int
              | CSet [(String, Type)]
    deriving (Eq, Ord, Show)

data NatModifier = Ordered | Discrete
  deriving (Show, Ord, Eq)

data CKind = CConstr Id | CPoly Id
    deriving (Eq, Ord, Show)
