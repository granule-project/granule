{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

{-| This transform makes every definition have a 0-1
    arguments via currying, using lambdas where appropriate.

    For example
    @
        f x y = something x y
        f : Int -> Int -> Int -> Int
    @
    becomes
    @
        f : Int -> Int -> Int -> Int
        f x = (\y -> something x y)
    @

    likewise
    @
        f : Int -> Int -> Int
        f = (\x -> (\y -> x + y))
    @
    becomes
    @
        f : Int -> Int -> Int
        f x = (\y -> x + y)
    @
  |-}
module Language.Granule.Codegen.NormalisedDef where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Pattern (Pattern)
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers (Id)
import Language.Granule.Syntax.FirstParameter
import GHC.Generics

data ValueDef v a =
    ValueDef {
        valueDefSpan :: Span,
        valueDefIdentifier :: Id,
        valueDefInitializer :: (Expr v a),
        valueDefTypeScheme :: TypeScheme }
    deriving Generic

instance (Pretty v) => Pretty (ValueDef v a) where
    prettyL l (ValueDef _ v e t) = prettyL l v <> " : " <> prettyL l t <> "\n" <>
                                   prettyL l v <> " = " <> prettyL l e

type FunctionDef v a = Def v a

instance FirstParameter (ValueDef v a) Span

deriving instance (Show a, Show v) => Show (ValueDef v a)
deriving instance (Eq a, Eq v) => Eq (ValueDef v a)

instance Definition (ValueDef v a) (Expr v a) where
    definitionSpan = valueDefSpan
    definitionIdentifier = valueDefIdentifier
    definitionBody = valueDefInitializer
    definitionTypeScheme = valueDefTypeScheme

isFunctionDef :: Def v a -> Bool
isFunctionDef = not . isValueDef

isValueDef :: Def v a -> Bool
isValueDef = null . defArguments

toValueDef :: Def v a -> ValueDef v a
toValueDef (Def sp ident expr _ ts) = (ValueDef sp ident expr ts)

data NormalisedAST v a =
    NormalisedAST [DataDecl] [FunctionDef v a] [ValueDef v a]
deriving instance (Show a, Show v) => Show (NormalisedAST v a)
deriving instance (Eq a, Eq v) => Eq (NormalisedAST v a)

normaliseDefinitionsPass :: AST ev Type -> NormalisedAST ev Type
normaliseDefinitionsPass (AST dd defs) =
    let normalisedDefs = map normaliseDefinition defs
        functionDefs = filter isFunctionDef normalisedDefs
        valueDefs = [toValueDef def | def <- normalisedDefs, isValueDef def]
    in (NormalisedAST dd functionDefs valueDefs)

normaliseDefinition :: Def ev Type -> Def ev Type
normaliseDefinition def@Def { defArguments = [] } = tryHoistLambda def
normaliseDefinition def@Def { defArguments = [_] } = def
normaliseDefinition def = curryDefinition def

tryHoistLambda :: Def ev Type -> Def ev Type
tryHoistLambda def@Def { defBody = (Val _ _ (Abs _ arg _ ex)) } =
    def { defArguments = [arg], defBody = ex }
tryHoistLambda def = def

curryDefinition :: Def ev Type -> Def ev Type
curryDefinition def =
    let (defArg:otherArgs) = defArguments def
        body = defBody def
        body' = argsToLambda otherArgs body (definitionType def)
    in def { defArguments = [defArg], defBody = body' }

argsToLambda :: [Pattern Type] -> Expr ev Type -> Type -> Expr ev Type
argsToLambda args originalBody ty =
    foldr wrapInLambda originalBody args
    where sp = getSpan originalBody
          wrapInLambda arg body = let bodyType = annotation body
                                      absType = (FunTy (annotation arg) bodyType)
                                  in Val sp absType (Abs absType arg Nothing body)
