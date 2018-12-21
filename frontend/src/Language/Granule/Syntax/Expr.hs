{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Expr where

import GHC.Generics (Generic)
import Control.Monad (forM)
import Control.Arrow
import Data.Text (Text)
import Data.List ((\\))

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

-- | Values in Granule that are extensible with values `v`
-- | and can have annotations 'a', though leaf value do not need
-- | an annotation since this should be provided by a `Val` constructor
-- | in an expression
data Value v a = Abs a (Pattern a) (Maybe Type) (Expr v a)
           | NumInt Int
           | NumFloat Double
           | Promote a (Expr v a)
           | Pure a (Expr v a)
           | Var a Id
           | Constr a Id [Value v a]
           | CharLiteral Char
           | StringLiteral Text
           -- Extensible part
           | Ext a v
   deriving (Generic)

instance FirstParameter (Value v a) a
deriving instance Show v => Show (Value v ())
deriving instance Functor (Value v)

-- | Expressions (computations) in Granule (with `v` extended values
-- | and annotations `a`).
data Expr v a =
    App Span a (Expr v a) (Expr v a)
  | Binop Span a Operator (Expr v a) (Expr v a)

  | LetDiamond Span a (Pattern a) (Maybe Type) (Expr v a) (Expr v a)
     -- Graded monadic composition (like Haskell do)
     -- let p : t <- e1 in e2
     -- or
     -- let p <- e1 in e2

  | Val Span a (Value v a)
  | Case Span a (Expr v a) [(Pattern a, Expr v a)]
  deriving (Generic)

deriving instance (Show (Value v a), Show a) => Show (Expr v a)
deriving instance Functor (Expr v)

instance FirstParameter (Expr v a) Span
instance SecondParameter (Expr v a) a

getAnnotation :: Expr v a -> a
getAnnotation = getSecondParameter

-- Syntactic sugar constructor
letBox :: Span -> Pattern () -> Expr v () -> Expr v () -> Expr v ()
letBox s pat e1 e2 =
  App s () (Val s () (Abs () (PBox s () pat) Nothing e2)) e1

pair :: Span -> Expr v () -> Expr v () -> Expr v ()
pair s e1 e2 = App s () (App s () (Val s () (Constr () (mkId "(,)") [])) e1) e2


class Substitutable t where
  -- Syntactic substitution of a term into an expression
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr v a -> Id -> t v a -> Expr v a


instance Term (Value v a) where
    freeVars (Abs _ p _ e) = freeVars e \\ boundVars p
    freeVars (Var _ x)     = [x]
    freeVars (Pure _ e)    = freeVars e
    freeVars (Promote _ e) = freeVars e
    freeVars NumInt{}        = []
    freeVars NumFloat{}      = []
    freeVars Constr{}        = []
    freeVars CharLiteral{}   = []
    freeVars StringLiteral{} = []
    freeVars Ext{} = []

instance Substitutable Value where
    subst es v (Abs a w t e)      = Val nullSpan a $ Abs a w t (subst es v e)
    subst es v (Pure a e)         = Val nullSpan a $ Pure a (subst es v e)
    subst es v (Promote a e)      = Val nullSpan a $ Promote a (subst es v e)
    subst es v (Var a w) | v == w = es
    subst _ _ v@NumInt{}        = Val nullSpan (getFirstParameter v) v
    subst _ _ v@NumFloat{}      = Val nullSpan (getFirstParameter v) v
    subst _ _ v@Var{}           = Val nullSpan (getFirstParameter v) v
    subst _ _ v@Constr{}        = Val nullSpan (getFirstParameter v) v
    subst _ _ v@CharLiteral{}   = Val nullSpan (getFirstParameter v) v
    subst _ _ v@StringLiteral{} = Val nullSpan (getFirstParameter v) v
    subst _ _ v@Ext{} = Val nullSpan (getFirstParameter v) v

instance Monad m => Freshenable m (Value v a) where
    freshen (Abs a p t e) = do
      p'   <- freshen p
      e'   <- freshen e
      t'   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      removeFreshenings (boundVars p')
      return $ Abs a p' t' e'

    freshen (Pure a e) = do
      e' <- freshen e
      return $ Pure a e'

    freshen (Promote a e) = do
      e' <- freshen e
      return $ Promote a e'

    freshen (Var a v) = do
      v' <- lookupVar Value v
      case v' of
         Just v' -> return (Var a $ Id (sourceName v) v')
         -- This case happens if we are referring to a defined
         -- function which does not get its name freshened
         Nothing -> return (Var a $ Id (sourceName v) (sourceName v))

    freshen v@NumInt{}   = return v
    freshen v@NumFloat{} = return v
    freshen v@Constr{}   = return v
    freshen v@CharLiteral{} = return v
    freshen v@StringLiteral{} = return v

instance Term (Expr v a) where
    freeVars (App _ _ e1 e2)            = freeVars e1 <> freeVars e2
    freeVars (Binop _ _ _ e1 e2)        = freeVars e1 <> freeVars e2
    freeVars (LetDiamond _ _ p _ e1 e2) = freeVars e1 <> (freeVars e2 \\ boundVars p)
    freeVars (Val _ _ e)                = freeVars e
    freeVars (Case _ _ e cases)         = freeVars e <> (concatMap (freeVars . snd) cases
                                      \\ concatMap (boundVars . fst) cases)

instance Substitutable Expr where
    subst es v (App s a e1 e2) =
      App s a (subst es v e1) (subst es v e2)

    subst es v (Binop s a op e1 e2) =
      Binop s a op (subst es v e1) (subst es v e2)

    subst es v (LetDiamond s a w t e1 e2) =
      LetDiamond s a w t (subst es v e1) (subst es v e2)

    subst es v (Val _ _ val) =
      subst es v val

    subst es v (Case s a expr cases) =
      Case s a (subst es v expr)
               (map (second (subst es v)) cases)

instance Monad m => Freshenable m (Expr v a) where
    freshen (App s a e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ App s a e1 e2

    freshen (LetDiamond s a p t e1 e2) = do
      e1 <- freshen e1
      p  <- freshen p
      e2 <- freshen e2
      t   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      return $ LetDiamond s a p t e1 e2

    freshen (Binop s a op e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ Binop s a op e1 e2

    freshen (Case s a expr cases) = do
      expr     <- freshen expr
      cases <- forM cases $ \(p, e) -> do
                  p <- freshen p
                  e <- freshen e
                  removeFreshenings (boundVars p)
                  return (p, e)
      return (Case s a expr cases)

    freshen (Val s a v) = do
     v <- freshen v
     return (Val s a v)
