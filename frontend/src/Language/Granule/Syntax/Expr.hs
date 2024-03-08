{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

{-# options_ghc -Wno-missing-pattern-synonym-signatures #-}

module Language.Granule.Syntax.Expr where

import GHC.Generics (Generic)
import Control.Monad (forM)
import Control.Arrow
import Data.Text (Text)
import Data.List ((\\))
import Data.Bifunctor.TH
import Data.Bifunctor hiding (second)
import Data.Bifunctor.Foldable (Base, Birecursive, project)
import qualified Text.Reprinter as Rp hiding (Generic)

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
    | NecF a expr
    | ConstrF a Id [value]
    | VarF a Id
    | NumIntF Int
    | NumFloatF Double
    | CharLiteralF Char
    | StringLiteralF Text
    | PackF Span a Type expr Id Kind Type
     -- pack <t, e> as exists {x : k} . t
    | TyAbsF a (Either (Id, Type) [Id]) expr
     -- /\(x : k) . t
    -- Extensible part
    | ExtF a ev
   deriving (Generic, Eq, Rp.Data)

deriving instance (Show ev, Show a, Show value, Show expr)
    => Show (ValueF ev a value expr)

$(deriveBifunctor ''ValueF)
$(deriveBifoldable ''ValueF)
$(deriveBitraversable ''ValueF)

type Value = ExprFix2 ValueF ExprF
type UnfixedValue ev a = UnExprFix2 ValueF ExprF ev a

pattern Abs :: a -> Pattern a -> Maybe Type -> ExprFix2 g ValueF ev a -> ExprFix2 ValueF g ev a
pattern Abs a arg mty ex = (ExprFix2 (AbsF a arg mty ex))

pattern Promote :: a -> ExprFix2 g ValueF ev a -> ExprFix2 ValueF g ev a
pattern Promote a ex = (ExprFix2 (PromoteF a ex))

pattern Pure :: a -> ExprFix2 g ValueF ev a -> ExprFix2 ValueF g ev a
pattern Pure a ex = (ExprFix2 (PureF a ex))

pattern Nec :: a -> ExprFix2 g ValueF ev a -> ExprFix2 ValueF g ev a
pattern Nec a ex = (ExprFix2 (NecF a ex))

pattern Constr :: a -> Id -> [ExprFix2 ValueF g ev a] -> ExprFix2 ValueF g ev a
pattern Constr a ident vals = (ExprFix2 (ConstrF a ident vals))

pattern Var :: a -> Id -> ExprFix2 ValueF g ev a
pattern Var a ident = (ExprFix2 (VarF a ident))

pattern NumInt :: Int -> ExprFix2 ValueF g ev a
pattern NumInt n = (ExprFix2 (NumIntF n))

pattern NumFloat :: Double -> ExprFix2 ValueF g ev a
pattern NumFloat n = (ExprFix2 (NumFloatF n))

pattern CharLiteral :: Char -> ExprFix2 ValueF g ev a
pattern CharLiteral ch = (ExprFix2 (CharLiteralF ch))

pattern StringLiteral :: Text -> ExprFix2 ValueF g ev a
pattern StringLiteral str = (ExprFix2 (StringLiteralF str))

pattern Pack :: Span
    -> a
    -> Type
    -> ExprFix2 g ValueF ev a
    -> Id
    -> Type
    -> Type
    -> ExprFix2 ValueF g ev a
pattern Pack sp a ty e x k ty' = ExprFix2 (PackF sp a ty e x k ty')

pattern TyAbs ::
      a
   -> Either (Id, Type) [Id]
   -> ExprFix2 g ValueF ev a
   -> ExprFix2 ValueF g ev a
pattern TyAbs a xt e = ExprFix2 (TyAbsF a xt e)

pattern Ext :: a -> ev -> ExprFix2 ValueF g ev a
pattern Ext a extv = (ExprFix2 (ExtF a extv))
{-# COMPLETE Abs, Promote, Pure, Constr, Var, NumInt,
             NumFloat, CharLiteral, StringLiteral, Pack, TyAbs, Ext #-}

-- | Expressions (computations) in Granule (with `v` extended values
-- | and annotations `a`).
data ExprF ev a expr value =
    AppF Span a Bool expr expr
  | AppTyF Span a Bool expr Type
  | BinopF Span a Bool Operator expr expr
  | LetDiamondF Span a Bool (Pattern a) (Maybe Type) expr expr
     -- Graded monadic composition (like Haskell do)
     -- let p : t <- e1 in e2
     -- or
     -- let p <- e1 in e2
  | TryCatchF Span a Bool expr (Pattern a) (Maybe Type) expr expr
     -- try e1 as p : t in e2 catch e3
  | ValF Span a Bool value
  | CaseF Span a Bool expr [(Pattern a, expr)]
  -- | HoleF Span a Bool [Id]
  | UnpackF Span a Bool Id Id expr expr
     -- unpack <a, x> = e1 in e2
  | HoleF Span a Bool [Id] (Maybe Hints)
  deriving (Generic, Eq, Rp.Data)

data Operator
  = OpLesser
  | OpLesserEq
  | OpGreater
  | OpGreaterEq
  | OpEq
  | OpNotEq
  | OpPlus
  | OpTimes
  | OpDiv
  | OpMinus
  deriving (Generic, Eq, Ord, Show, Rp.Data)


data Hints =
  Hints {
    hSubtractive :: Bool,
    hPruning     :: Bool,
    hNoTimeout   :: Bool,
    hLinHaskell  :: Maybe Span, -- The location of the hole in the original Haskell file
    hTimeout     :: Maybe Int,
    hIndex       :: Maybe Int
  }
  deriving (Generic, Eq, Show, Rp.Data)


deriving instance (Show ev, Show a, Show value, Show expr)
    => Show (ExprF ev a value expr)

$(deriveBifunctor ''ExprF)
$(deriveBifoldable ''ExprF)
$(deriveBitraversable ''ExprF)

type Expr = ExprFix2 ExprF ValueF
type UnfixedExpr ev a = UnExprFix2 ExprF ValueF ev a

pattern App :: Span
               -> a
               -> Bool
               -> ExprFix2 ExprF g ev a
               -> ExprFix2 ExprF g ev a
               -> ExprFix2 ExprF g ev a
pattern App sp a rf fexp argexp = (ExprFix2 (AppF sp a rf fexp argexp))

pattern AppTy :: Span
                 -> a
                 -> Bool
                 -> ExprFix2 ExprF g ev a
                 -> Type
                 -> ExprFix2 ExprF g ev a
pattern AppTy sp a rf fexp ty = (ExprFix2 (AppTyF sp a rf fexp ty))

pattern Binop :: Span
                 -> a
                 -> Bool
                 -> Operator
                 -> ExprFix2 ExprF g ev a
                 -> ExprFix2 ExprF g ev a
                 -> ExprFix2 ExprF g ev a
pattern Binop sp a rf op lhs rhs = (ExprFix2 (BinopF sp a rf op lhs rhs))

pattern LetDiamond :: Span
                      -> a
                      -> Bool
                      -> Pattern a
                      -> Maybe Type
                      -> ExprFix2 ExprF g ev a
                      -> ExprFix2 ExprF g ev a
                      -> ExprFix2 ExprF g ev a
pattern LetDiamond sp a rf pat mty nowexp nextexp = (ExprFix2 (LetDiamondF sp a rf pat mty nowexp nextexp))

pattern TryCatch :: Span
                    -> a
                    -> Bool
                    -> ExprFix2 ExprF g ev a
                    -> Pattern a
                    -> Maybe Type
                    -> ExprFix2 ExprF g ev a
                    -> ExprFix2 ExprF g ev a
                    -> ExprFix2 ExprF g ev a
pattern TryCatch sp a rf t1 pat mty t2 t3 = (ExprFix2 (TryCatchF sp a rf t1 pat mty t2 t3))

pattern Val :: Span -> a -> Bool -> ExprFix2 g ExprF ev a -> ExprFix2 ExprF g ev a
pattern Val sp a rf val = (ExprFix2 (ValF sp a rf val))

pattern Case :: --forall {g :: * -> * -> * -> * -> *} {ev} {a}.
                Span
                -> a
                -> Bool
                -> ExprFix2 ExprF g ev a
                -> [(Pattern a, ExprFix2 ExprF g ev a)]
                -> ExprFix2 ExprF g ev a
pattern Case sp a rf swexp arms = (ExprFix2 (CaseF sp a rf swexp arms))


pattern Unpack :: Span
    -> a
    -> Bool
    -> Id
    -> Id
    -> ExprFix2 ExprF g ev a
    -> ExprFix2 ExprF g ev a
    -> ExprFix2 ExprF g ev a
pattern Unpack sp a rf tyVar var e1 e2 = ExprFix2 (UnpackF sp a rf tyVar var e1 e2)



pattern Hole :: -- forall {g :: * -> * -> * -> * -> *} {ev} {a}.
                Span
                -> a
                -> Bool
                -> [Id]
                -> Maybe Hints
                -> ExprFix2 ExprF g ev a
pattern Hole sp a rf vs hs = ExprFix2 (HoleF sp a rf vs hs)

{-# COMPLETE App, Binop, LetDiamond, TryCatch, Val, Case, Hole, Unpack #-}

-- Cannot be automatically derived unfortunately
instance Functor (Value ev) where
  fmap f (Abs a pats mt e) = Abs (f a) (fmap f pats) mt (fmap f e)
  fmap f (Promote a e)     = Promote (f a) (fmap f e)
  fmap f (Pure a e)        = Pure (f a) (fmap f e)
  fmap f (Nec a e)         = Nec (f a) (fmap f e)
  fmap f (Constr a idv vals) = Constr (f a) idv (map (fmap f) vals)
  fmap f (Var a idv)       = Var (f a) idv
  fmap f (Ext a ev)        = Ext (f a) ev
  fmap f (NumInt n)        = NumInt n
  fmap f (NumFloat n)      = NumFloat n
  fmap f (CharLiteral c)   = CharLiteral c
  fmap f (StringLiteral s) = StringLiteral s
  fmap f (Pack s a ty e1 var k ty') =
    Pack s (f a) ty (fmap f e1) var k ty'
  fmap f (TyAbs a vart e) =
    TyAbs (f a) vart (fmap f e)

instance Functor (Expr ev) where
  fmap f (App s a rf e1 e2) = App s (f a) rf (fmap f e1) (fmap f e2)
  fmap f (AppTy s a rf e1 t) = AppTy s (f a) rf (fmap f e1) t
  fmap f (Binop s a b op t1 t2) = Binop s (f a) b op (fmap f t1) (fmap f t2)
  fmap f (LetDiamond s a b ps mt e1 e2) = LetDiamond s (f a) b (fmap f ps) mt (fmap f e1) (fmap f e2)
  fmap f (TryCatch s a b e p mt e1 e2) = TryCatch s (f a) b (fmap f e) (fmap f p) mt (fmap f e1) (fmap f e2)
  fmap f (Val s a b val) = Val s (f a) b (fmap f val)
  fmap f (Case s a b expr pats) = Case s (f a) b (fmap f expr) (map (\(p, e) -> (fmap f p, fmap f e)) pats)
  fmap f (Unpack s a rf tyVar var e1 e2) =
    Unpack s (f a) rf tyVar var (fmap f e1) (fmap f e2)
  fmap f (Hole s a b ids hints)  = Hole s (f a) b ids hints

instance Bifunctor (f ev a)
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

instance Rp.Refactorable (Expr ev a) where
  isRefactored (App _ _ True _ _) = Just Rp.Replace
  isRefactored (Binop _ _ True _ _ _) = Just Rp.Replace
  isRefactored (LetDiamond _ _ True _ _ _ _) = Just Rp.Replace
  isRefactored (TryCatch _ _ True _ _ _ _ _) = Just Rp.Replace
  isRefactored (Val _ _ True _) = Just Rp.Replace
  isRefactored (Case _ _ True _ _) = Just Rp.Replace
  isRefactored (Hole _ _ True _ _) = Just Rp.Replace
  isRefactored _ = Nothing

  getSpan = convSpan . getFirstParameter

deriving instance (Rp.Data (ExprFix2 ValueF ExprF () ()))
deriving instance ((Rp.Data (ExprFix2 ValueF ExprF ev a)), Rp.Data ev, Rp.Data a) => Rp.Data (Expr ev a)

-- Syntactic sugar constructor
letBox :: Span -> Pattern () -> Expr ev () -> Expr ev () -> Expr ev ()
letBox s pat e1 e2 =
  App s () False (Val s () False (Abs () (PBox s () False pat) Nothing e2)) e1

pair :: Expr v () -> Expr v () -> Expr v ()
pair e1 e2 = App s () False (App s () False (Val s () False (Constr () (mkId "(,)") [])) e1) e2
             where s = nullSpanNoFile

typedPair :: Value v Type -> Value v Type -> Value v Type
typedPair left right =
    Constr ty (mkId "(,)") [left, right]
    where ty = pairType leftType rightType
          leftType = annotation left
          rightType = annotation right

pairType :: Type -> Type -> Type
pairType leftType rightType =
    TyApp (TyApp (TyCon (Id "," ",")) leftType) rightType

-- let p = e1 in e2
letExpr :: Span -> Pattern () -> Expr ev () -> Expr ev () -> Expr ev ()
letExpr s p e1 e2 = App s () False (Val s () False (Abs () p Nothing e2)) e1

class Substitutable t where
  -- Syntactic substitution of a term into an expression
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr ev a -> Id -> t ev a -> Expr ev a

instance Term (Value ev a) where
    freeVars (Abs _ p _ e) = freeVars e \\ boundVars p
    freeVars (Var _ x)     = [x]
    freeVars (Pure _ e)    = freeVars e
    freeVars (Promote _ e) = freeVars e
    freeVars (Nec _ e)    = freeVars e
    freeVars NumInt{}        = []
    freeVars NumFloat{}      = []
    freeVars Constr{}        = []
    freeVars CharLiteral{}   = []
    freeVars StringLiteral{} = []
    freeVars Ext{} = []
    freeVars (Pack s a ty e1 var k ty') = freeVars e1
    freeVars (TyAbs a _ e) = freeVars e

    hasHole (Abs _ _ _ e) = hasHole e
    hasHole (Pure _ e)    = hasHole e
    hasHole (Promote _ e) = hasHole e
    hasHole (Nec _ e)    = hasHole e
    hasHole (Pack s a ty e1 var k ty') = hasHole e1
    hasHole _             = False

    isLexicallyAtomic Abs{} = False
    isLexicallyAtomic (Constr _ s xs) = null xs || internalName s == ","
    isLexicallyAtomic _     = True

instance Substitutable Value where
    subst es v (Abs a w t e)      = Val (nullSpanInFile $ getSpan es) a False $ Abs a w t (subst es v e)
    subst es v (Pure a e)         = Val (nullSpanInFile $ getSpan es) a False $ Pure a (subst es v e)
    subst es v (Promote a e)      = Val (nullSpanInFile $ getSpan es) a False $ Promote a (subst es v e)
    subst es v (Nec a e)          = Val (nullSpanInFile $ getSpan es) a False $ Nec a (subst es v e)
    subst es v (Var a w) | v == w = es
    subst es _ v@NumInt{}        = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@NumFloat{}      = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@Var{}           = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@Constr{}        = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@CharLiteral{}   = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@StringLiteral{} = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es _ v@Ext{} = Val (nullSpanInFile $ getSpan es) (getFirstParameter v) False v
    subst es v (Pack s a ty e var k ty') =
      Val (nullSpanInFile $ getSpan es) a False $ Pack s a ty (subst es v e) var k ty'
    subst es v (TyAbs a vart e) =
      Val (nullSpanInFile $ getSpan es) a False $ TyAbs a vart (subst es v e)

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

    freshen (Nec a e) = do
      e' <- freshen e
      return $ Nec a e'

    freshen (Var a v) = do
      v' <- lookupVar ValueL v
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

    freshen (Pack s a ty e1 var k ty') = do
      e1  <- freshen e1
      ty  <- freshen ty
      var <- freshIdentifierBase TypeL var
      k   <- freshen k
      ty' <- freshen ty'
      return $ Pack s a ty e1 var k ty'

    freshen (TyAbs a (Left (v, t)) e) = do
      v <- freshIdentifierBase TypeL v
      e <- freshen e
      t <- freshen t
      return $ TyAbs a (Left (v, t)) e

    freshen (TyAbs a (Right ids) e) = do
        ids <- mapM freshen' ids
        e   <- freshen e
        return $ TyAbs a (Right ids) e
      where
        freshen' id = do
          id' <- freshen (TyVar id)
          case id' of
            TyVar id' -> return id'
            _ -> error "Internal bug in freshener for type abstraction"


freshenId :: Monad m => Id -> Freshener m Id
freshenId v = do
      v' <- lookupVar ValueL v
      case v' of
         Just v' -> return (Id (sourceName v) v')
         -- This case happens if we are referring to a defined
         -- function which does not get its name freshened
         Nothing -> return (Id (sourceName v) (sourceName v))

instance Term (Expr v a) where
    freeVars (App _ _ _ e1 e2)            = freeVars e1 <> freeVars e2
    freeVars (AppTy _ _ _ e1 e2)          = freeVars e1 <> freeVars e2
    freeVars (Binop _ _ _ _ e1 e2)        = freeVars e1 <> freeVars e2
    freeVars (LetDiamond _ _ _ p _ e1 e2) = freeVars e1 <> (freeVars e2 \\ boundVars p)
    freeVars (TryCatch _ _ _ e1 p _ e2 e3) = freeVars e1 <> (freeVars e2 \\ boundVars p) <> freeVars e3
    freeVars (Val _ _ _ e)                = freeVars e
    freeVars (Case _ _ _ e cases)         = freeVars e <> (concatMap (freeVars . snd) cases
                                      \\ concatMap (boundVars . fst) cases)
    freeVars (Unpack s a _ tyVar var e1 e2) =
      freeVars e1 <> (freeVars e2 \\ [tyVar, var])
    freeVars (Hole _ _ _ vars _) = vars

    hasHole (App _ _ _ e1 e2) = hasHole e1 || hasHole e2
    hasHole (AppTy _ _ _ e _) = hasHole e
    hasHole (Binop _ _ _ _ e1 e2) = hasHole e1 || hasHole e2
    hasHole (LetDiamond _ _ _ p _ e1 e2) = hasHole e1 || hasHole e2
    hasHole (TryCatch _ _ _ e1 p _ e2 e3) = hasHole e1 || hasHole e2 || hasHole e3
    hasHole (Val _ _ _ e) = hasHole e
    hasHole (Case _ _ _ e cases) = hasHole e || (or (map (hasHole . snd) cases))
    hasHole Hole{} = True
    hasHole (Unpack s a _ tyVar var e1 e2) = hasHole e1 || hasHole e2

    isLexicallyAtomic (Val _ _ _ e) = isLexicallyAtomic e
    isLexicallyAtomic (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ x _)) t1) t2) = sourceName x == ","
    isLexicallyAtomic _ = False

instance Substitutable Expr where
    subst es v (App s a rf e1 e2) =
      App s a rf (subst es v e1) (subst es v e2)

    subst es v (AppTy s a rf e1 t) =
      AppTy s a rf (subst es v e1) t

    subst es v (Binop s a rf op e1 e2) =
      Binop s a rf op (subst es v e1) (subst es v e2)

    subst es v (LetDiamond s a rf w t e1 e2) =
      LetDiamond s a rf w t (subst es v e1) (subst es v e2)

    subst es v (TryCatch s a rf e1 p t e2 e3) =
      TryCatch s a rf (subst es v e1) p t (subst es v e2) (subst es v e3)

    subst es v (Val _ _ _ val) =
      subst es v val

    subst es v (Case s a rf expr cases) =
      Case s a rf (subst es v expr)
               (map (second (subst es v)) cases)

    subst es _ v@Hole{} = v

    subst es v (Unpack s a rf tyVar var e1 e2) =
      Unpack s a rf tyVar var (subst es v e1) (subst es v e2)

instance Monad m => Freshenable m (Expr v a) where
    freshen (App s a rf e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ App s a rf e1 e2

    freshen (AppTy s a rf e1 t) = do
      e1 <- freshen e1
      t <- freshen t
      return $ AppTy s a rf e1 t

    freshen (LetDiamond s a rf p t e1 e2) = do
      e1 <- freshen e1
      p  <- freshen p
      e2 <- freshen e2
      t   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      return $ LetDiamond s a rf p t e1 e2

    freshen (TryCatch s a rf e1 p t e2 e3) = do
      e1 <- freshen e1
      p <- freshen p
      t   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      e2 <- freshen e2
      e3 <- freshen e3
      return $ TryCatch s a rf e1 p t e2 e3

    freshen (Binop s a rf op e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ Binop s a rf op e1 e2

    freshen (Case s a rf expr cases) = do
      expr     <- freshen expr
      cases <- forM cases $ \(p, e) -> do
                  p <- freshen p
                  e <- freshen e
                  removeFreshenings (boundVars p)
                  return (p, e)
      return (Case s a rf expr cases)

    freshen (Val s a rf v) = do
     v <- freshen v
     return (Val s a rf v)

    freshen (Hole s a rf vars hints) = do
      -- Freshen hole variables like they are normal variables
      vars' <- mapM freshenId vars
      return $ Hole s a rf vars' hints

    freshen (Unpack s a rf tyVar var e1 e2) = do
      e1    <- freshen e1
      tyVar <- freshIdentifierBase TypeL tyVar
      var   <- freshIdentifierBase ValueL var
      e2    <- freshen e2
      removeFreshenings [var]
      return $ Unpack s a rf tyVar var e1 e2

-- If an expression is a right-nested application tree on a contructor then
-- extract the head constructor and the list of parameters
constructorApplicationSpine :: Expr e a -> Maybe (Id, [Expr e a])

constructorApplicationSpine (Val s' a' b' (Constr _ c vs)) =
  Just (c, map (Val s' a' b') vs)

constructorApplicationSpine (App _ _ _ (Val s' a' b' (Constr _ c vs)) e) =
  -- Left-most constructor application found
  Just (c, map (Val s' a' b') vs ++ [e])

constructorApplicationSpine (App _ _ _ e1 e2) = do
  -- Node
  (cname, args) <- constructorApplicationSpine e1
  Just (cname, args ++ [e2])

constructorApplicationSpine _ =
  Nothing