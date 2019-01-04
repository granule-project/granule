{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.ConvertClosuresSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck
import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.ConvertClosures
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type hiding (var)
import Language.Granule.Utils
import Debug.Trace

import Language.Granule.Codegen.BuildAST

cap :: String -> Int -> Type -> Value ClosureMarkerValue Type
cap ident n ty = Ext ty $ CapturedVar ty (mkId ident) n

globals :: [String] -> [Id]
globals = map mkId

env :: String -> [Type] -> Maybe NamedClosureEnvironmentType
env name types =
    Just (name, TyClosureEnvironment types)

makeClosure :: (Definition d ClosureFreeExpr)
            => d
            -> String
            -> [ClosureVariableInit]
            -> ClosureFreeExpr
makeClosure def envName inits =
    val $ Ext ty $ MakeClosure defIdent $ ClosureEnvironmentInit envName inits
    where ty = definitionType def
          defIdent = definitionIdentifier def

parent :: String -> Type -> Int -> ClosureVariableInit
parent n ty i = FromParentEnv (mkId n) ty i

local :: String -> Type -> ClosureVariableInit
local n ty = FromLocalScope (mkId n) ty

closureFreeASTFromDefs :: [ClosureFreeFunctionDef] -> [ClosureFreeValueDef] -> ClosureFreeAST
closureFreeASTFromDefs functionDefs valueDefs =
    ClosureFreeAST [] functionDefs valueDefs

defclos  :: String
         -> Pattern Type
         -> Maybe NamedClosureEnvironmentType
         -> Expr ClosureMarkerValue Type
         -> TypeScheme
         -> ClosureFreeFunctionDef
defclos name arg env bodyexpr ts =
    FunctionDef {
        closureFreeDefSpan = nullSpan,
        closureFreeDefIdentifier = mkId name,
        closureFreeDefEnvironment = env,
        closureFreeDefBody = bodyexpr,
        closureFreeDefArgument = arg,
        closureFreeDefTypeScheme = ts }


spec :: Test.Spec
spec = do
  describe "closure conversion" $ do
    let ?globals = defaultGlobals
    it "works correctly for two arg add" $ do
        let original = normASTFromDefs
                            [defun "add" [arg "x" int]
                                (lambdaexp (arg "y" int) (int .-> int)
                                     ((val (var "x" int)) `plus` (val (var "y" int))))
                                (tts $ int .-> int .-> int)]
                            []
        let expected = closureFreeASTFromDefs [add, lambda0] []
                       where lambda0 =
                                 defclos "lambda.0" (arg "y" int) (env "lambda.0.env" [int])
                                    ((val (cap "x" 0 int)) `plus` (val (var "y" int)))
                                    (tts $ int .-> int)
                             add =
                                 defclos "add" (arg "x" int) Nothing
                                    (makeClosure lambda0 "lambda.0.env" [local "x" int])
                                    (tts $ int .-> int .-> int)
        convertClosuresInAST original `shouldBe` expected
    it "doesn't capture globals" $ do
        let original = normASTFromDefs
                           [defun "add" [arg "x" int]
                               (lambdaexp (arg "y" int) (int .-> int)
                                   ((val (var "x" int)) `plus`
                                   (val (var "y" int)) `plus`
                                   (val (var "g" int))))
                                   (tts $ int .-> int .-> int)]
                           [defval "g" (val (lit 10)) (tts int)]
        let expected = closureFreeASTFromDefs [add, lambda0] [g]
                       where lambda0 =
                                 defclos "lambda.0" (arg "y" int) (env "lambda.0.env" [int])
                                    ((val (cap "x" 0 int)) `plus`
                                     (val (var "y" int)) `plus`
                                     (val (var "g" int)))
                                    (tts $ int .-> int)
                             add =
                                 defclos "add" (arg "x" int) Nothing
                                    (makeClosure lambda0 "lambda.0.env" [local "x" int])
                                    (tts $ int .-> int .-> int)
                             g = defval "g" (val (lit 10)) (tts int)
        convertClosuresInAST original `shouldBe` expected
    it "ensures second occurence has same index as first" $ do
        let original = normASTFromDefs
                           [defun "add" [arg "x" int]
                               (lambdaexp (arg "y" int) (int .-> int)
                                    ((val (var "x" int)) `plus`
                                     (val (var "x" int)) `plus`
                                     (val (var "y" int))))
                               (tts $ int .-> int .-> int)]
                           []
        let expected = closureFreeASTFromDefs [add, lambda0] []
                       where add = defclos "add" (arg "x" int) Nothing
                                       (makeClosure lambda0 "lambda.0.env" [local "x" int])
                                       (tts $ int .-> int .-> int)
                             lambda0 = defclos "lambda.0" (arg "y" int) (env "lambda.0.env" [int])
                                           ((val (cap "x" 0 int)) `plus`
                                            (val (cap "x" 0 int)) `plus`
                                            (val (var "y" int)))
                                           (tts $ int .-> int)
        convertClosuresInAST original `shouldBe` expected
    it "handles nested lambdas" $ do
        let original = normASTFromDefs
                           [defun "add" [arg "x" int]
                               (lambdaexp (arg "y" int) (int .-> int .-> int)
                                    (lambdaexp (arg "z" int) (int .-> int)
                                        ((val (var "y" int)) `plus`
                                         (val (var "x" int)) `plus`
                                         (val (var "z" int)))))
                               (tts $ int .-> int .-> int .-> int)]
                           []
        let expected = closureFreeASTFromDefs [add, lambda0, lambda1] []
                       where add =     defclos "add" (arg "x" int) Nothing
                                           (makeClosure lambda1 "lambda.1.env" [local "x" int])
                                           (tts $ int .-> int .-> int .-> int)
                             lambda1 = defclos "lambda.1" (arg "y" int) (env "lambda.1.env" [int])
                                           (makeClosure lambda0 "lambda.0.env" [parent "x" int 0, local "y" int])
                                           (tts $ int .-> int .-> int)
                             lambda0 = defclos "lambda.0" (arg "z" int) (env "lambda.0.env" [int, int])
                                           ((val (cap "y" 1 int)) `plus`
                                            (val (cap "x" 0 int)) `plus`
                                            (val (var "z" int)))
                                           (tts $ int .-> int)
        convertClosuresInAST original `shouldBe` expected
