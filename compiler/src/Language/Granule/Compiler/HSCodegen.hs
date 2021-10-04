-- | Generate Haskell code from Granule

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-typed-holes #-}
module Language.Granule.Compiler.HSCodegen where

import Control.Monad
import Data.Functor

import Language.Granule.Compiler.Util as Hs
import Language.Granule.Compiler.Gensym
import Language.Granule.Compiler.Context

import Language.Granule.Syntax.Def as GrDef
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Expr as GrExpr
import Language.Granule.Syntax.Type as GrType
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.FirstParameter

cgDefs :: MonadGensym m => AST ev GrType.Type -> m [Decl ()]
cgDefs (AST dd defs imports _ _) =
  do defs' <- mapM cgDef  defs <&> concat
     dd'   <- mapM cgData dd   <&> concat
     return $ defs' ++ dd'

cgDef :: MonadGensym m => Def ev GrType.Type -> m [Decl ()]
cgDef _ = return []

cgData :: MonadGensym m => DataDecl -> m [Decl ()]
cgData _ = return []

cgTypeScheme :: MonadGensym m => TypeScheme -> m (Hs.Type ())
cgTypeScheme (Forall _ binders constraints typ) = undefined

cgType :: MonadGensym m => GrType.Type -> m (Hs.Type ())
cgType (GrType.Type i) = return mkUnit
cgType (GrType.FunTy _ t1 t2) = do
  t1' <- cgType t1
  t2' <- cgType t2
  return $ Hs.TyFun () t1' t2'
cgType (GrType.TyCon i) =
  return $ Hs.TyCon () $ UnQual () $ name $ internalName i
cgType (GrType.Box t t2) = return mkUnit
cgType (GrType.Diamond t t2) = return mkUnit
cgType (GrType.TyVar i) =
  return $ Hs.TyVar () $ name $ internalName i
cgType (GrType.TyApp t1 t2) = do
  t1' <- cgType t1
  t2' <- cgType t2
  return $ Hs.TyApp () t1' t2'
cgType (GrType.TyInt i) = return mkUnit
cgType (GrType.TyRational ri) = return mkUnit
cgType (GrType.TyGrade mt i) = return mkUnit
cgType (GrType.TyInfix t t2 t3) = error "cgType: not implemented"
cgType (GrType.TySet p l_t) = return mkUnit
cgType (GrType.TyCase t l_p_tt) = error "cgType: not implemented"
cgType (GrType.TySig t t2) = error "cgType: not implemented"

type CExpr = GrExpr.Expr () ()

cgExpr :: MonadGensym m => CExpr -> m (Exp ())
cgExpr = error "cgExpr: not implemented"
-- cgExpr (GrExpr.App s _ _ e1 e2) = _
-- cgExpr (GrExpr.AppTy s _ _ e t) = _
-- cgExpr (GrExpr.Binop _ _ _ op e1 e2) = _
-- cgExpr (GrExpr.LetDiamond s _ _ p _ e1 e2) = _
-- cgExpr (GrExpr.TryCatch s _ _ e1 p _ e2 e3) = _
-- cgExpr (GrExpr.Val _ _ _ e) = _
-- cgExpr (GrExpr.Case s a b guardExpr cases) = _
-- cgExpr GrExpr.Hole{} = _
