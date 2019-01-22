{-# LANGUAGE LambdaCase #-}
module Language.Granule.Codegen.ConvertClosures where

import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Data.Set (Set)
import Data.List (findIndex)
import Data.Maybe (fromJust, fromMaybe)
import Data.Bifunctor.Foldable
import Data.Bifoldable
import qualified Data.Set as Set

import Control.Monad.State
import Control.Monad.Writer

convertClosures :: NormalisedAST () Type -> ClosureFreeAST
convertClosures (NormalisedAST dataDecl functionDefs valueDefs) =
    let globals = (definitionIdentifier <$> functionDefs) ++ (definitionIdentifier <$> valueDefs)
        ((functionDefs', valueDefs'), lambdaDefs) =
            evalLiftLambda $ do
                values <- mapM (convertClosuresInValueDef globals) valueDefs
                functions <- mapM (convertClosuresInFunctionDef globals) functionDefs
                return (functions, values)
    in ClosureFreeAST dataDecl (functionDefs' ++ lambdaDefs) valueDefs'

convertClosuresInFunctionDef :: [Id] -> FunctionDef () Type -> LiftLambdaM ClosureFreeFunctionDef
convertClosuresInFunctionDef globals (FunctionDef sp ident body arg ts) =
    do
        let locals = boundVars arg
        body' <- convertClosuresInExpression globals locals body
        return $ ClosureFreeFunctionDef sp ident Nothing body' arg ts

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
          boundFromExpr (Case _ _ _ arms) (x, y, bound) =
              (x, y, bound ++ boundByArms arms)
          boundFromExpr _ bound = bound
          boundFromValue (Abs _ arg _ body) (_, parentEnvironment, parentLocals) =
              let locals           = boundVars arg
                  initializer      = environmentInitializer globals parentEnvironment parentLocals locals body
                  maybeInitializer = if null initializer then Nothing else Just initializer
              in (parentEnvironment, maybeInitializer, locals)
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
variableInitializer locals parentEnv var =
    error $ "Invalid combination of arguments to generate initializer \n"
            ++ (show locals) ++ "\n" ++ (show parentEnv) ++ "\n" ++ (show var)

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
          -- NOTE: This marks all names bound by every match as bound in every arm.
          -- Which is not technically correct but should be ok because of the
          -- freshener.
          accumBoundValue _ bound = bound
          accumBoundExpr (Case _ _ _ arms) bound = bound ++ boundByArms arms
          accumBoundExpr (LetDiamond _ _ pattern _ _ _) bound = bound ++ (boundVars pattern)
          accumBoundExpr _ bound = bound


boundByArms :: [(Pattern a, b)] -> [Id]
boundByArms = concatMap (boundVars . fst)


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
        let lambdaName = "lambda#" ++ show index
        let envName = "env." ++ lambdaName
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
convertClosuresFromValue globals (_, maybeCurrentEnv, _) (AbsF ty@(FunTy _ _) arg mty expr) =
    do
        (lambdaIdent, envName) <- freshLambdaIdentifiers
        let lambdaTypeScheme = Forall nullSpanNoFile [] ty
        let envTy = environmentType envName maybeCurrentEnv
        let lambdaDef = ClosureFreeFunctionDef nullSpanNoFile lambdaIdent envTy expr arg lambdaTypeScheme
        lift $ tell [lambdaDef]
        return $ Ext ty $
            case maybeCurrentEnv of
                Just env -> MakeClosure lambdaIdent (ClosureEnvironmentInit envName env)
                Nothing  -> MakeTrivialClosure lambdaIdent

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
