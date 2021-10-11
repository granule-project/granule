-- | Generate Haskell code from Granule

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-typed-holes #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Granule.Compiler.HSCodegen where

import Control.Monad
import Data.Functor
import Control.Monad.State
import Control.Monad.Except

import Language.Granule.Compiler.Util as Hs
import Language.Granule.Compiler.Error

import Language.Granule.Syntax.Def as GrDef
import Language.Granule.Syntax.Pattern as GrPat
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Expr as GrExpr
import Language.Granule.Syntax.Type as GrType
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.FirstParameter
import Data.Text (unpack)

import Debug.Trace

type CExpr = GrExpr.Expr  () ()
type CVal  = GrExpr.Value () ()
type CPat  = GrPat.Pattern   ()
type CAst  = AST          () ()

type Compiler m = MonadError CompilerError m

cg :: CAst -> Either CompilerError String
cg ast = join (runExceptT (do mod <- cgModule ast
                              return $ prettyPrint mod))

cgModule :: Compiler m => CAst -> m (Module ())
cgModule ast = do
  decls <- cgDefs ast
  return $ Module () Nothing [grPragmas] [grImport] decls

cgDefs :: Compiler m => CAst -> m [Decl ()]
cgDefs (AST dd defs imports _ _) =
  do defs' <- mapM cgDef  defs <&> concat
     dd'   <- mapM cgData dd   <&> concat
     return $ dd' ++ defs'

cgDef :: Compiler m => Def () () -> m [Decl ()]
cgDef (Def _ id _ EquationList{equations} typeschemes) = do
  scheme <- cgTypeScheme typeschemes
  let bodies = map equationBody     equations
      pats   = map equationPatterns equations
  pats'   <- mapM cgPats  pats
  bodies' <- mapM cgExpr bodies
  let cases = zip pats' bodies'
      impl = mkEquation (name $ sourceName id) cases
      sig  = TypeSig () [name $ sourceName id] scheme
  return [sig,impl]

cgData :: Compiler m => DataDecl -> m [Decl ()]
cgData (GrDef.DataDecl _ id tyvars _ constrs) = do
  conDecls <- mapM cgDataConstr constrs
  let dhead = foldr ((\i a -> DHApp () a $ UnkindedVar () i) . (name . internalName . fst))
                    (DHead () (name $ internalName id)) tyvars
  return [Hs.DataDecl () (DataType ()) Nothing dhead conDecls []]

cgDataConstr :: Compiler m => DataConstr -> m (QualConDecl ())
cgDataConstr (DataConstrIndexed s i t) = unsupported "cgData: indexed data cons not supported"
cgDataConstr (DataConstrNonIndexed _ i tys) = do
  tys' <- mapM cgType tys
  return $ QualConDecl () Nothing Nothing $ ConDecl () (name $ sourceName i) tys'

cgTypeScheme :: Compiler m => TypeScheme -> m (Hs.Type ())
cgTypeScheme (Forall _ binders constraints typ) = cgType typ
  -- unsupported "cgTypeScheme: not implemented"

cgPats :: Compiler m => [CPat] -> m [Pat ()]
cgPats = mapM cgPat

cgPat :: Compiler m => CPat -> m (Pat ())
cgPat (GrPat.PVar _ _ _ i) =
  return $ Hs.PVar () $ name $ sourceName i
cgPat GrPat.PWild{} =
  return $ PWildCard ()
cgPat (GrPat.PBox _ _ _ pt) =
  cgPat pt
cgPat (GrPat.PInt _ _ _ n) =
  return $ PLit () (Signless ()) $ Int () (fromIntegral n) (show n)
cgPat (GrPat.PFloat _ _ _ n) =
  return $ PLit () (Signless ()) $ Frac () (toRational n) (show n)
cgPat (GrPat.PConstr _ _ _ i l_pt)
  | i == Id "," ","  = do
      pts <- mapM cgPat l_pt
      return $ pTuple pts
  | otherwise = do
      pts <- mapM cgPat l_pt
      return $ PApp () (UnQual () $ name $ sourceName i) pts

cgType :: Compiler m => GrType.Type -> m (Hs.Type ())
cgType (GrType.Type i) = return $ TyStar ()
cgType (GrType.FunTy _ t1 t2) = do
  t1' <- cgType t1
  t2' <- cgType t2
  return $ Hs.TyFun () t1' t2'
cgType (GrType.TyCon i) =
  return $ Hs.TyCon () $ UnQual () $ name $ sourceName i
cgType (GrType.Box t t2) = cgType t2
cgType (GrType.Diamond t t2) = do
  t2' <- cgType t2
  return $ Hs.TyApp () (Hs.TyCon () $ UnQual () $ name "IO") t2'
cgType (GrType.TyVar i) =
  return $ Hs.TyVar () $ name $ sourceName i
cgType (GrType.TyApp t1 t2) =
  if isTupleType t1
  then cgTypeTuple t1 t2
  else do
    t1' <- cgType t1
    t2' <- cgType t2
    return $ Hs.TyApp () t1' t2'
cgType (GrType.TyInt i) = return mkUnit
cgType (GrType.TyRational ri) = return mkUnit
cgType (GrType.TyGrade mt i) = return mkUnit
cgType (GrType.TyInfix t t2 t3) = unsupported "cgType: tyinfix not implemented"
cgType (GrType.TySet p l_t) = return mkUnit
cgType (GrType.TyCase t l_p_tt) = unsupported "cgType: tycase not implemented"
cgType (GrType.TySig t t2) = unsupported "cgType: tysig not implemented"

isTupleType :: GrType.Type -> Bool
isTupleType (GrType.TyApp (GrType.TyCon id) _) = id == Id "," ","
isTupleType _oth = False

cgTypeTuple :: Compiler m => GrType.Type -> GrType.Type -> m (Hs.Type ())
cgTypeTuple (GrType.TyApp (GrType.TyCon _id) t1) t2 = do
  t1' <- cgType t1
  t2' <- cgType t2
  return $ TyTuple () Boxed [t1', t2']
cgTypeTuple _ _ = error "expected tuple"

cgExpr :: Compiler m => CExpr -> m (Exp ())
cgExpr (GrExpr.App _ _ _ e1 e2) =
  if isTupleExpr e1
  then cgExprTuple e1 e2
  else do
  e1' <- cgExpr e1
  e2' <- cgExpr e2
  return $ app e1' e2'
cgExpr (GrExpr.AppTy _ _ _ e t) = unsupported "cgExpr: not implemented"
cgExpr (GrExpr.Binop _ _ _ op e1 e2) = do
  e1' <- cgExpr e1
  e2' <- cgExpr e2
  cgBinop op e1' e2'
cgExpr (GrExpr.LetDiamond _ _ _ p _ e1 e2) = do
  p' <- cgPat p
  e1' <- cgExpr e1
  e2' <- cgExpr e2
  let lam = lamE [p'] e2'
  return $ infixApp e1' (op $ sym ">>=") lam
cgExpr (GrExpr.TryCatch _ _ _ e1 p _ e2 e3) = unsupported "cgExpr: not implemented"
cgExpr (GrExpr.Val _ _ _ e) = cgVal e
cgExpr (GrExpr.Case _ _ _ guardExpr cases) = unsupported "cgExpr: not implemented"
cgExpr GrExpr.Hole{} = error "cgExpr: not implemented"

isTupleExpr :: CExpr -> Bool
isTupleExpr (GrExpr.App _ _ _ (GrExpr.Val _ _ _ (GrExpr.Constr _ i _)) _) = i == Id "," ","
isTupleExpr _ = False

cgExprTuple :: Compiler m => CExpr -> CExpr -> m (Exp ())
cgExprTuple (GrExpr.App _ _ _ (GrExpr.Val _ _ _ (GrExpr.Constr _ i _)) e1) e2 = do
  e1' <- cgExpr e1
  e2' <- cgExpr e2
  return $ tuple [e1', e2']
cgExprTuple _ _ = error "expected tuple"

cgVal :: Compiler m => CVal -> m (Exp ())
cgVal (Promote _ty ex) = cgExpr ex
cgVal (Pure ty ex) = error "cgVal: not implemented"
cgVal (GrExpr.Var _ty i)  =
  return $ Hs.Var () $ UnQual () $ name $ sourceName i
cgVal (NumInt n) =
  return $ Hs.Lit () $ Int () (fromIntegral n) (show n)
cgVal (NumFloat n) =
  return $ Hs.Lit () $ Frac () (toRational n) (show n)
cgVal (CharLiteral ch) =
  return $ Hs.Lit () $ Char () ch (show ch)
cgVal (StringLiteral str) =
  return $ Hs.Lit () $ Hs.String () (unpack str) (unpack str)
cgVal (Constr _ i vals) = do
  vals' <- mapM cgVal vals
  let con = Con () (UnQual () $ name $ sourceName i)
  return $ appFun con vals'
cgVal (Abs _ p _ ex) = do
  p' <- cgPat p
  ex' <- cgExpr ex
  return $ lamE [p'] ex'
cgVal Ext{} = unexpected "cgVal: unexpected Ext"


cgBinop :: Compiler m => Operator -> Exp () -> Exp () -> m (Exp ())
cgBinop OpLesser e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "<"))) e2
cgBinop OpLesserEq e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "<="))) e2
cgBinop OpGreater e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym ">"))) e2
cgBinop OpGreaterEq e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym ">="))) e2
cgBinop OpEq e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "=="))) e2
cgBinop OpNotEq e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "/="))) e2
cgBinop OpPlus e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "+"))) e2
cgBinop OpTimes e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "*"))) e2
cgBinop OpDiv e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "/"))) e2
cgBinop OpMinus e1 e2 =
  return $ InfixApp () e1 (QVarOp () (UnQual () (sym "-"))) e2
