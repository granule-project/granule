{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

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
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.FirstParameter
import Data.Either (lefts, rights)
import Data.List (transpose)
import GHC.Generics

data NormalisedAST v a =
    NormalisedAST [DataDecl] [FunctionDef v a] [ValueDef v a]

deriving instance (Show a, Show v) => Show (NormalisedAST v a)
deriving instance (Eq a, Eq v) => Eq (NormalisedAST v a)

data ValueDef v a =
    ValueDef {
        valueDefSpan :: Span,
        valueDefIdentifier :: Id,
        valueDefInitializer :: (Expr v a),
        valueDefTypeScheme :: TypeScheme }
    deriving Generic
deriving instance (Show a, Show v) => Show (ValueDef v a)
deriving instance (Eq a, Eq v) => Eq (ValueDef v a)

instance Definition (ValueDef v a) where
    definitionSpan = valueDefSpan
    definitionIdentifier = valueDefIdentifier
    definitionTypeScheme = valueDefTypeScheme

data FunctionDef v a =
    FunctionDef {
        functionDefSpan :: Span,
        functionDefIdentifier :: Id,
        functionDefBody :: Expr v a,
        functionDefArgument :: Pattern a,
        functionDefTypeScheme :: TypeScheme }
    deriving Generic
deriving instance (Show a, Show v) => Show (FunctionDef v a)
deriving instance (Eq a, Eq v) => Eq (FunctionDef v a)

instance Definition (FunctionDef v a) where
    definitionSpan = functionDefSpan
    definitionIdentifier = functionDefIdentifier
    definitionTypeScheme = functionDefTypeScheme

instance (Pretty v) => Pretty (ValueDef v a) where
    prettyL l (ValueDef _ v e t) = prettyL l v <> " : " <> prettyL l t <> "\n" <>
                                   prettyL l v <> " = " <> prettyL l e

instance Pretty v => Pretty (FunctionDef v a) where
    prettyL l (FunctionDef _ v e ps t) = prettyL l v <> " : " <> prettyL l t <> "\n" <>
                                         prettyL l v <> " " <> prettyL l ps <> "= " <> prettyL l e

instance FirstParameter (ValueDef v a) Span

normaliseDefinitions :: AST ev Type -> NormalisedAST ev Type
normaliseDefinitions (AST dd defs) =
    let normalisedDefs = map normaliseDefinition defs
    in NormalisedAST dd (lefts normalisedDefs) (rights normalisedDefs)

normaliseDefinition :: Def ev Type -> Either (FunctionDef ev Type) (ValueDef ev Type)
normaliseDefinition def  =
    let singleEquationDef = makeSingleEquationWithCase def
        equation          = normaliseEquation (head $ defEquations singleEquationDef)
        normalisedDef     = singleEquationDef { defEquations = [equation] }
    in case normalisedDef of
           d | isValueDef d    -> Right $ toValueDef normalisedDef
           d | isFunctionDef d -> Left  $ toFunctionDef normalisedDef

isFunctionDef :: Def v a -> Bool
isFunctionDef = not . isValueDef

isValueDef :: Def v a -> Bool
isValueDef Def { defEquations = [equation] } =
    null $ equationArguments equation
isValueDef _ = False

toValueDef :: Def v a -> ValueDef v a
toValueDef (Def sp ident [equation] ts) =
    ValueDef {
        valueDefSpan = sp,
        valueDefIdentifier = ident,
        valueDefInitializer = equationBody equation,
        valueDefTypeScheme = ts }

toFunctionDef :: Def ev a -> FunctionDef ev a
toFunctionDef (Def sp ident [caseEquation] ts) =
    FunctionDef {
        functionDefSpan = sp,
        functionDefIdentifier = ident,
        functionDefBody = equationBody caseEquation,
        functionDefArgument = head $ equationArguments caseEquation,
        functionDefTypeScheme = ts }

makeSingleEquationWithCase :: Def ev Type -> Def ev Type
makeSingleEquationWithCase def@(Def sp ident [eq] ts) = def
makeSingleEquationWithCase def@(Def sp ident eqs ts) =
    let equation = Equation sp (definitionType def) irrefutableArgs generatedCaseExpr
                   where irrefutableArgs     = makeIrrefutableArgs casePatterns
                         generatedCaseExpr   = makeCaseExpr irrefutableArgs (casePatterns, caseExprs)
                         casePatterns        = map equationArguments eqs
                         caseExprs           = map equationBody eqs
    in def { defEquations = [equation] }

makeIrrefutableArgs :: [[Pattern Type]] -> [Pattern Type]
makeIrrefutableArgs patternLists =
    zipWith patternForArg [1..] (transpose patternLists)

-- | Assumes best name is the last in the list.
-- | If there are no irrefutable matches the name is arg.n.
patternForArg :: Int -> [Pattern Type] -> Pattern Type
patternForArg n patterns =
    let patternTy = annotation $ head patterns
        defaultPattern = PVar nullSpanNoFile patternTy (mkId $ "arg." ++ show n)
        accumulateBestName irrefutablePat@(PVar _ _ ident) bestName = irrefutablePat
        accumulateBestName reffutablePat bestName                   = bestName
    in foldr accumulateBestName defaultPattern patterns

makeCaseExpr :: [Pattern Type]
             -> ([[Pattern Type]], [Expr ev Type])
             -> Expr ev Type
makeCaseExpr irrefutableArgPatterns (casePatterns, caseExprs) =
    Case nullSpanNoFile ty (Val nullSpanNoFile (annotation sw) sw) branches
    where branches       = zip (map mergePatterns casePatterns) caseExprs
          ty             = annotation (head caseExprs)
          sw         = mergeArguments $ boundVarsAndAnnotations $
                               mergePatterns irrefutableArgPatterns

-- | x, y, z -> ((x, y), z)
mergePatterns :: [Pattern Type] -> Pattern Type
mergePatterns (firstPattern:remainingPatterns) =
    foldl patternPair firstPattern remainingPatterns
    where patternPair left right = ppair nullSpanNoFile (pairType (annotation left) (annotation right)) left right
          patternPair :: Pattern Type -> Pattern Type -> Pattern Type

mergeArguments :: [(Type, Id)] -> Value ev Type
mergeArguments argumentsIds =
    let firstArg:otherArgs = map (\(ty, ident) -> Var ty ident) argumentsIds
    in foldl typedPair firstArg otherArgs

normaliseEquation :: Equation ev Type -> Equation ev Type
normaliseEquation eq@Equation { equationArguments = [] } = tryHoistLambda eq
normaliseEquation eq@Equation { equationArguments = [_] } = eq
normaliseEquation eq = curryEquation eq

tryHoistLambda :: Equation ev Type -> Equation ev Type
tryHoistLambda eq@Equation { equationBody = (Val _ _ (Abs _ arg _ ex)) } =
    eq { equationArguments = [arg], equationBody = ex }
tryHoistLambda def = def

curryEquation :: Equation ev Type -> Equation ev Type
curryEquation eq =
    let (eqArg:otherArgs) = equationArguments eq
        body = equationBody eq
        body' = argsToLambda otherArgs body (equationType eq)
    in eq { equationArguments = [eqArg], equationBody = body' }

argsToLambda :: [Pattern Type] -> Expr ev Type -> Type -> Expr ev Type
argsToLambda args originalBody ty =
    foldr wrapInLambda originalBody args
    where sp = getSpan originalBody
          wrapInLambda arg body = let bodyType = annotation body
                                      absType = (FunTy (annotation arg) bodyType)
                                  in Val sp absType (Abs absType arg Nothing body)
