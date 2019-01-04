{-# LANGUAGE LambdaCase #-}
module Language.Granule.Codegen.ConvertClosures where

import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern (boundVars)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Data.Set (Set)
import Data.List (findIndex)
import Data.Maybe (fromJust, fromMaybe)
import Data.Bifunctor.Foldable
import Data.Bifoldable
import qualified Data.Set as Set

import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class

convertClosuresInAST :: NormalisedAST () Type -> ClosureFreeAST
convertClosuresInAST (NormalisedAST dataDecl functionDefs valueDefs) =
    let globals = (definitionIdentifier <$> functionDefs) ++ (definitionIdentifier <$> valueDefs)
        ((functionDefs', valueDefs'), lambdaDefs) =
            evalLiftLambda $ do
                values <- mapM (convertClosuresInValueDef globals) valueDefs
                functions <- mapM (convertClosuresInFunctionDef globals) functionDefs
                return (functions, values)
    in ClosureFreeAST dataDecl (functionDefs' ++ lambdaDefs) valueDefs'

convertClosuresInFunctionDef :: [Id] -> FunctionDef () Type -> LiftLambdaM ClosureFreeFunctionDef
convertClosuresInFunctionDef globals (Def sp ident body [arg] ts) =
    do
        let locals = boundVars arg
        body' <- convertClosuresInExpression globals locals body
        return $ FunctionDef sp ident Nothing body' arg ts
convertClosuresInFunctionDef _ _ =
    error "Attempted to lambda lift definition with multiple arguments."

convertClosuresInValueDef :: [Id] -> ValueDef () Type -> LiftLambdaM ClosureFreeValueDef
convertClosuresInValueDef globals (ValueDef sp ident initExpr ts) =
    do
        initExpr' <- convertClosuresInExpression globals [] initExpr
        return $ ValueDef sp ident initExpr' ts

type LiftLambdaM a = StateT Int (Writer [ClosureFreeFunctionDef]) a

evalLiftLambda :: LiftLambdaM a -> (a, [ClosureFreeFunctionDef])
evalLiftLambda s = runWriter $ evalStateT s 0

convertClosuresInExpression :: [Id]
                        -> [Id]
                        -> Expr () Type
                        -> LiftLambdaM ClosureFreeExpr
convertClosuresInExpression globals locals =
    bicataPM (convertClosuresFromExpr, boundFromExpr)
             (liftFromValue, boundFromValue)
             (Nothing, Nothing, locals)
    where liftFromValue = convertClosuresFromValue globals
          boundFromExpr _ ctx = ctx
          boundFromValue (Abs _ arg _ body) (_, parentEnvironment, parentLocals) =
              let locals = boundVars arg
                  initializer = environmentInitializer globals parentEnvironment parentLocals locals body
              in (parentEnvironment, Just initializer, locals)
          boundFromValue _ ctx = ctx

environmentInitializer :: [Id]
                       -> Maybe [ClosureVariableInit]
                       -> [Id]
                       -> [Id]
                       -> Expr ev Type
                       -> [ClosureVariableInit]
environmentInitializer globals parentEnvironment parentLocals locals expr =
    let capturedVars = Set.toList (captures globals locals expr)
    in map (variableInitializer parentLocals parentEnvironment) capturedVars

variableInitializer :: [Id]
                    -> Maybe [ClosureVariableInit]
                    -> (Type, Id)
                    -> ClosureVariableInit
variableInitializer locals _ (ty, ident)
    | ident `elem` locals =
        FromLocalScope ident ty
variableInitializer _ (Just parentEnvironment) (ty, ident) =
    case findCaptureIndex parentEnvironment ident of
        Just n -> FromParentEnv ident ty n
        Nothing -> error $ "Attempt to capture " ++ (show ident) ++
                           " which is not in the parent environment or local scope."
variableInitializer local cvis var =
    error $ "Invalid combination of arguments to generate initializer \n"
            ++ (show local) ++ "\n" ++ (show cvis) ++ "\n" ++ (show var)

findCaptureIndex :: [ClosureVariableInit] -> Id -> Maybe Int
findCaptureIndex env ident =
    findIndex hasIdent env
    where hasIdent (FromParentEnv i _ _) = ident == i
          hasIdent (FromLocalScope i _)  = ident == i

captures :: [Id] -> [Id] -> Expr ev Type -> Set (Type, Id)
captures globals locals ex =
    bicataP (capturesInExpr, accumBoundExpr) (capturesInValue, accumBoundValue) locals ex
    where capturesInExpr _ expr = bifold expr
          capturesInValue bound (VarF ty ident)
              | not (ident `elem` bound || ident `elem` globals) =
                  Set.singleton (ty, ident)
              | otherwise =
                  Set.empty
          capturesInValue _ val = bifold val
          accumBoundValue (Abs _ arg _ expr) bound = bound ++ (boundVars arg)
          accumBoundValue _ bound = bound
          accumBoundExpr _ bound = bound

convertClosuresFromExpr :: (Maybe [ClosureVariableInit], Maybe [ClosureVariableInit], [Id])
                    -> ExprF ev Type ClosureFreeExpr ClosureFreeValue
                    -> LiftLambdaM ClosureFreeExpr
convertClosuresFromExpr _ expr =
    return $ case expr of
                AppF sp ty fn arg -> App sp ty fn arg
                BinopF sp ty op lhs rhs -> Binop sp ty op lhs rhs
                LetDiamondF sp ty pat mty now next ->
                    LetDiamond sp ty pat mty now next
                ValF sp ty val -> Val sp ty val
                CaseF sp ty swexp arms -> Case sp ty swexp arms

freshLambdaIdentifiers :: LiftLambdaM (Id, String)
freshLambdaIdentifiers =
    do
        index <- get
        modify (+1)
        let lambdaName = "lambda." ++ show index
        let envName = lambdaName ++ ".env"
        return (mkId lambdaName, envName)

environmentType :: String
                -> Maybe [ClosureVariableInit]
                -> Maybe NamedClosureEnvironmentType
environmentType name maybeVariableInitializers =
    maybeVariableInitializers >>=
        \case
            [] -> Nothing
            variableInitializers ->
                let types = map closureVariableInitType variableInitializers
                in Just (name, TyClosureEnvironment types)

convertClosuresFromValue :: [Id]
                     -> (Maybe [ClosureVariableInit], Maybe [ClosureVariableInit], [Id])
                     -> ValueF ev Type ClosureFreeValue ClosureFreeExpr
                     -> LiftLambdaM ClosureFreeValue
convertClosuresFromValue globals (_, maybeCurrentEnv, _) (AbsF ty arg mty expr) =
    do
        (lambdaIdent, envName) <- freshLambdaIdentifiers
        let lambdaTypeScheme = Forall nullSpan [] ty
        let envTy = environmentType envName maybeCurrentEnv
        let lambdaDef = FunctionDef nullSpan lambdaIdent envTy expr arg lambdaTypeScheme
        lift $ tell [lambdaDef]
        return $ maybe (Ext ty $ MakeTrivialClosure lambdaIdent) (\env ->
            let initializer = ClosureEnvironmentInit envName env
            in Ext ty $ MakeClosure lambdaIdent initializer) maybeCurrentEnv

convertClosuresFromValue globals (_, maybeCurrentEnv, locals) (VarF ty ident)
    | (not $ ident `elem` locals || ident `elem` globals) =
        let currentEnv = fromJust maybeCurrentEnv
            indexInEnv = fromMaybe errorMessage (findCaptureIndex currentEnv ident)
                         where errorMessage = error $ "Could not find captured variable "
                                              ++ (sourceName ident) ++ " in environment."
        in return $ Ext ty (CapturedVar ty ident indexInEnv)
convertClosuresFromValue globals _ other =
    return $
        case other of
            VarF ty ident -> Var ty ident
            PromoteF ty expr -> Promote ty expr
            PureF ty expr -> Pure ty expr
            ConstrF ty ident vs -> Constr ty ident vs
            NumIntF n -> NumInt n
            NumFloatF f -> NumFloat f
            CharLiteralF c -> CharLiteral c
            StringLiteralF t -> StringLiteral t
            ExtF ty ev ->
                error "Extension value found in AST before closure conversion."
            _ -> error "Unexpected AST Node."
