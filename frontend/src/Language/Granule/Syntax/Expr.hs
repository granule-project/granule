{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Granule.Syntax.Expr where

import GHC.Generics (Generic)
import Control.Monad (forM)
import Control.Arrow
import Data.Text (Text)
import Data.List ((\\))
import Data.Bifunctor.TH
import Data.Bifunctor hiding (second)
import Data.Bifunctor.Foldable (Base, Birecursive, project)

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

newtype ExprFix2 f g ev a = ExprFix2 { unExprFix :: UnExprFix2 f g ev a }
type UnExprFix2 f g ev a = (f ev a (ExprFix2 f g ev a) (ExprFix2 g f ev a))

instance Show (UnExprFix2 f g ev a) => Show (ExprFix2 f g ev a) where
    showsPrec n x = showsPrec 11 (unExprFix x)

instance Eq (UnExprFix2 f g ev a) => Eq (ExprFix2 f g ev a) where
    a == b = (unExprFix a) == (unExprFix b)

-- | Values in Granule that are extensible with values `ev`
-- | and can have annotations 'a', though leaf values do not need
-- | an annotation since this should be provided by a `Val` constructor
-- | in an expression
data ValueF ev a value expr =
      AbsF a (Pattern a) (Maybe Type) expr
    | PromoteF a expr
    | PureF a expr
    | ConstrF a Id [value]
    | VarF a Id
    | NumIntF Int
    | NumFloatF Double
    | CharLiteralF Char
    | StringLiteralF Text
    -- Extensible part
    | ExtF a ev
   deriving (Generic, Eq)

deriving instance (Show ev, Show a, Show value, Show expr)
    => Show (ValueF ev a value expr)

$(deriveBifunctor ''ValueF)
$(deriveBifoldable ''ValueF)
$(deriveBitraversable ''ValueF)

type Value = ExprFix2 ValueF ExprF
type UnfixedValue ev a = UnExprFix2 ValueF ExprF ev a

pattern Abs a arg mty ex = (ExprFix2 (AbsF a arg mty ex))
pattern Promote a ex = (ExprFix2 (PromoteF a ex))
pattern Pure a ex = (ExprFix2 (PureF a ex))
pattern Constr a ident vals = (ExprFix2 (ConstrF a ident vals))
pattern Var a ident = (ExprFix2 (VarF a ident))
pattern NumInt n = (ExprFix2 (NumIntF n))
pattern NumFloat n = (ExprFix2 (NumFloatF n))
pattern CharLiteral ch = (ExprFix2 (CharLiteralF ch))
pattern StringLiteral str = (ExprFix2 (StringLiteralF str))
pattern Ext a extv = (ExprFix2 (ExtF a extv))
{-# COMPLETE Abs, Promote, Pure, Constr, Var, NumInt,
             NumFloat, CharLiteral, StringLiteral, Ext #-}

-- | Expressions (computations) in Granule (with `v` extended values
-- | and annotations `a`).
data ExprF ev a expr value =
    AppF Span a expr expr
  | BinopF Span a Operator expr expr
  | LetDiamondF Span a (Pattern a) (Maybe Type) expr expr
     -- Graded monadic composition (like Haskell do)
     -- let p : t <- e1 in e2
     -- or
     -- let p <- e1 in e2
  | ValF Span a value
  | CaseF Span a expr [(Pattern a, expr)]
  deriving (Generic, Eq)

deriving instance (Show ev, Show a, Show value, Show expr)
    => Show (ExprF ev a value expr)

$(deriveBifunctor ''ExprF)
$(deriveBifoldable ''ExprF)
$(deriveBitraversable ''ExprF)

type Expr = ExprFix2 ExprF ValueF
type UnfixedExpr ev a = UnExprFix2 ExprF ValueF ev a

pattern App sp a fexp argexp = (ExprFix2 (AppF sp a fexp argexp))
pattern Binop sp a op lhs rhs = (ExprFix2 (BinopF sp a op lhs rhs))
pattern LetDiamond sp a pat mty nowexp nextexp = (ExprFix2 (LetDiamondF sp a pat mty nowexp nextexp))
pattern Val sp a val = (ExprFix2 (ValF sp a val))
pattern Case sp a swexp arms = (ExprFix2 (CaseF sp a swexp arms))
{-# COMPLETE App, Binop, LetDiamond, Val, Case #-}

instance (Bifunctor (f ev a), Bifunctor (g ev a))
    => Birecursive (ExprFix2 f g ev a) (ExprFix2 g f ev a) where
    project = unExprFix

type instance Base (ExprFix2 f g ev a) (ExprFix2 g f ev a) = (f ev a)

instance FirstParameter (UnfixedValue ev a) a
instance FirstParameter (UnfixedExpr ev a) Span
instance SecondParameter (UnfixedExpr ev a) a

instance FirstParameter (Value ev a) a where
    getFirstParameter v = getFirstParameter $ unExprFix v
    setFirstParameter x v = ExprFix2 $ setFirstParameter x $ unExprFix v

instance FirstParameter (Expr ev a) Span where
    getFirstParameter e = getFirstParameter $ unExprFix e
    setFirstParameter x e = ExprFix2 $ setFirstParameter x $ unExprFix e

instance SecondParameter (Expr ev a) a where
    getSecondParameter e = getSecondParameter $ unExprFix e
    setSecondParameter x e = ExprFix2 $ setSecondParameter x $ unExprFix e

instance Annotated (Expr ev a) a where
    annotation = getSecondParameter

instance Annotated (Value ev Type) Type where
    annotation (NumInt _) = TyCon (mkId "Int")
    annotation (NumFloat _) = TyCon (mkId "Float")
    annotation (StringLiteral _) = TyCon (mkId "String")
    annotation (CharLiteral _) = TyCon (mkId "Char")
    annotation other = getFirstParameter other

-- Syntactic sugar constructor
letBox :: Span -> Pattern () -> Expr ev () -> Expr ev () -> Expr ev ()
letBox s pat e1 e2 =
  App s () (Val s () (Abs () (PBox s () pat) Nothing e2)) e1

pair :: Span -> Expr v () -> Expr v () -> Expr v ()
pair s e1 e2 = App s () (App s () (Val s () (Constr () (mkId ",") [])) e1) e2


class Substitutable t where
  -- Syntactic substitution of a term into an expression
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr ev a -> Id -> t ev a -> Expr ev a


instance Term (Value ev a) where
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
    subst es v (Abs a w t e)      = Val (nullSpanInFile $ getSpan es) a $ Abs a w t (subst es v e)
    subst es v (Pure a e)         = Val (nullSpanInFile $ getSpan es) a $ Pure a (subst es v e)
    subst es v (Promote a e)      = Val (nullSpanInFile $ getSpan es) a $ Promote a (subst es v e)
    subst es v (Var a w) | v == w = es
    subst es _ v@NumInt{}        = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@NumFloat{}      = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@Var{}           = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@Constr{}        = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@CharLiteral{}   = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@StringLiteral{} = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v
    subst es _ v@Ext{} = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) v

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
    freshen v@Ext{} = return v

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
