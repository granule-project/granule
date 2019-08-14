{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Granule.Codegen.ClosureFreeDef where
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.MarkGlobals
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Pattern
import Data.List (intercalate)
import GHC.Generics

newtype ClosureEnvironmentType =
    TyClosureEnvironment [Type]
    deriving (Show, Eq)

type NamedClosureEnvironmentType = (String, ClosureEnvironmentType)

data ClosureEnvironmentInit =
    ClosureEnvironmentInit String [ClosureVariableInit]
    deriving (Show, Eq)

data ClosureVariableInit =
    FromParentEnv Id Type Int
    | FromLocalScope Id Type
    deriving (Show, Eq, Ord)

closureVariableInitType :: ClosureVariableInit -> Type
closureVariableInitType (FromParentEnv _ ty _) = ty
closureVariableInitType (FromLocalScope _ ty) = ty

data ClosureFreeFunctionDef = ClosureFreeFunctionDef {
    closureFreeDefSpan :: Span,
    closureFreeDefIdentifier :: Id,
    closureFreeDefEnvironment :: Maybe NamedClosureEnvironmentType,
    closureFreeDefBody :: Expr (Either GlobalMarker ClosureMarker) Type,
    closureFreeDefArgument :: Pattern Type,
    closureFreeDefTypeScheme :: TypeScheme }
    deriving (Generic, Eq, Show)

type ClosureFreeExpr = Expr (Either GlobalMarker ClosureMarker) Type
type ClosureFreeValue = Value (Either GlobalMarker ClosureMarker) Type
type ClosureFreeValueDef = ValueDef (Either GlobalMarker ClosureMarker) Type

data ClosureMarker =
    CapturedVar Type Id Int
    | MakeClosure Id ClosureEnvironmentInit
    | MakeTrivialClosure Id
    deriving (Show, Eq)

data ClosureFreeAST =
    ClosureFreeAST [DataDecl] [ClosureFreeFunctionDef] [ClosureFreeValueDef]
    deriving (Show, Eq)

instance Pretty ClosureFreeAST where
    pretty (ClosureFreeAST dataDecls functionDefs valueDefs) =
        pretty' dataDecls <> "\n\n" <> pretty' functionDefs <> "\n\n" <> pretty' valueDefs
        where
            pretty' :: Pretty l => [l] -> String
            pretty' = intercalate "\n\n" . map pretty

instance Pretty ClosureFreeFunctionDef where
    pretty (ClosureFreeFunctionDef _ v env e ps t) = pretty v <> " : " <> pretty t <> "\n" <>
                              pretty v <> " " <> pretty ps <> " = " <> pretty e

instance Pretty ClosureMarker where
    pretty (CapturedVar _ty ident _n) =
        "env(" ++ pretty ident ++ ")"
    pretty (MakeClosure ident env) =
        let prettyEnvVar (FromParentEnv ident ty _) =
                "parent-env(" ++ pretty ident ++ ") : " ++ pretty ty
            prettyEnvVar (FromLocalScope ident ty) =
                pretty ident ++ " : " ++ pretty ty
            prettyEnv (ClosureEnvironmentInit envName varInits) =
                "env(ident = \"" ++ envName ++ "\", " ++ intercalate ", " (map prettyEnvVar varInits) ++ ")"
        in "make-closure(" ++ pretty ident ++ ", " ++ prettyEnv env ++ ")"
    pretty (MakeTrivialClosure ident) = pretty ident
