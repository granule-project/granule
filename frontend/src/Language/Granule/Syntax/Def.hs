{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Def where

import Data.List ((\\), delete)
import GHC.Generics (Generic)

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern

-- | Top-level ASTs
-- | Comprise a list of data type declarations and a list
-- | of expression definitions
-- | where `v` is the type of values and `a` annotations
data AST v a = AST [DataDecl] [Def v a]

deriving instance (Show (Def v a), Show a) => Show (AST v a)

class Definition d expr | d -> expr where
    definitionSpan :: d -> Span
    definitionIdentifier :: d -> Id
    definitionBody :: d -> expr
    definitionTypeScheme :: d -> TypeScheme

-- | Expression definitions
data Def v a = Def {
    defSpan :: Span,
    defIdentifier :: Id,
    defBody :: Expr v a,
    defArguments :: [Pattern a],
    defTypeScheme :: TypeScheme }
    deriving Generic

instance FirstParameter (Def v a) Span
deriving instance (Show a, Show v) => Show (Def v a)
deriving instance (Eq a, Eq v) => Eq (Def v a)

instance Definition (Def ev a) (Expr ev a) where
    definitionSpan = getSpan
    definitionIdentifier = defIdentifier
    definitionBody = defBody
    definitionTypeScheme = defTypeScheme

definitionType :: (Definition d expr) => d -> Type
definitionType def =
    ty where (Forall _ _ ty) = definitionTypeScheme def

-- | Data type declarations
data DataDecl = DataDecl {
    dataDeclSpan :: Span,
    dataDeclName :: Id,
    dataDeclMembers :: [(Id,Kind)],
    dataDeclKind :: (Maybe Kind),
    dataDeclConstructors :: [DataConstr] }
    deriving (Generic, Show, Eq)

instance FirstParameter DataDecl Span

-- | Data constructors
data DataConstr
  = DataConstrG Span Id TypeScheme -- ^ GADTs
  | DataConstrA Span Id [Type]     -- ^ ADTs
  deriving (Eq, Show, Generic)

instance FirstParameter DataConstr Span


-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat

-- | Fresh a whole AST
freshenAST :: AST v a -> AST v a
freshenAST (AST dds defs) = AST dds (map runFreshener defs)

{-| Alpha-convert all bound variables of a definition, modulo the things on the lhs
Eg this:
@
foo : Int -> Int
foo x = (\(x : Int) -> x * 2) x
@
will become
@
foo : Int -> Int
foo x = (\(x0 : Int) -> x0 * 2) x
@

>>> :{
runFreshener $ Def { defSpan = ((1,1),(2,29)),
                     defIdentifier = (Id "foo" "foo"),
                     defBody = (App ((2,10),(2,29)) ()
                               (Val ((2,10),(2,25)) ()
                                   (Abs () (PVar ((2,12),(2,12)) () (Id "x" "x0")) (Just (TyCon (Id "Int" "Int")))
                                       (Binop ((2,25),(2,25)) () "*"
                                           (Val ((2,24),(2,24)) () (Var () (Id "x" "x0")))
                                           (Val ((2,26),(2,26)) () (NumInt 2)))))
                               (Val ((2,29),(2,29)) () (Var () (Id "x" "x")))),
                     defArguments = [PVar ((2,5),(2,5)) () (Id "x" "x")],
                     defTypeScheme = (Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int")))) }
:}
Def {defSpan = ((1,1),(2,29)), defIdentifier = (Id "foo" "foo"), defBody = (AppF ((2,10),(2,29)) () (ValF ((2,10),(2,25)) () (AbsF () (PVar ((2,12),(2,12)) () (Id "x" "x_1")) (Just (TyCon (Id "Int" "Int"))) (BinopF ((2,25),(2,25)) () "*" (ValF ((2,24),(2,24)) () (VarF () (Id "x" "x_1"))) (ValF ((2,26),(2,26)) () (NumIntF 2))))) (ValF ((2,29),(2,29)) () (VarF () (Id "x" "x_0")))), defArguments = [PVar ((2,5),(2,5)) () (Id "x" "x_0")], defTypeScheme = Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int")))}
-}
instance Freshenable (Def v a) where
  freshen (Def s var e ps t) = do
    ps <- mapM freshen ps
    t  <- freshen t
    e  <- freshen e
    return (Def s var e ps t)

instance Term (Def v a) where
  freeVars (Def _ name body binders _) = delete name (freeVars body \\ concatMap boundVars binders)
