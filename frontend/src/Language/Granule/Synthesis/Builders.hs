{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

-- Helpers for synthesising terms

module Language.Granule.Synthesis.Builders where

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type

pattern ProdTy :: Type -> Type -> Type
pattern ProdTy t1 t2 = TyApp (TyApp (TyCon (Id "," ",")) t1) t2

pattern SumTy :: Type -> Type -> Type
pattern SumTy t1 t2  = TyApp (TyApp (TyCon (Id "Either" "Either")) t1) t2

makeVar :: Id -> TypeScheme -> Expr () Type
makeVar name (Forall _ _ _ t) =
  Val s t False (Var t name)
  where s = nullSpanNoFile

makeVarUntyped :: Id -> Expr () ()
makeVarUntyped name =
  Val s () False (Var () name)
  where s = nullSpanNoFile

makeAbs :: Id -> Expr () Type -> TypeScheme -> Expr () Type
makeAbs name e (Forall _ _ _ t@(FunTy _ _ t1 t2)) =
  Val s t False (Abs t (PVar s t False name) (Just t1) e)
  where s = nullSpanNoFile
makeAbs name e _ = error "Cannot synth here" -- TODO: better error handling

makeAbsUnbox :: Type -> Id -> Expr () Type -> TypeScheme -> Expr () Type
makeAbsUnbox t name e (Forall _ _ _ t'@(FunTy _ _ t1 t2)) =
  Val s t False (Abs t (PBox s t False (PVar s t' False name)) (Just t1) e)
  where s = nullSpanNoFile
makeAbsUnbox _ name e _ = error "Cannot synth here" -- TODO: better error handling

makeApp :: Id -> Expr () Type -> TypeScheme -> Type -> Expr () Type
makeApp name e (Forall _ _ _ t1) t2 =
  App s t1 False (makeVar name (Forall nullSpanNoFile [] [] t2)) e
  where s = nullSpanNoFile

makeBox :: TypeScheme -> Expr () Type -> Expr () Type
makeBox (Forall _ _ _ t) e =
  Val s t False (Promote t e)
  where s = nullSpanNoFile

makeBoxUntyped :: Expr () () -> Expr () ()
makeBoxUntyped e =
  Val s () False (Promote () e)
  where s = nullSpanNoFile

pbox :: Pattern () -> Pattern ()
pbox = PBox nullSpanNoFile () True

-- The first name is the name being bound by the let
-- The second name is the one that is the subject of the let
makeUnbox :: Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makeUnbox name1 name2 tyS boxTy varTy =
  makeUnboxP name1 (Val s varTy False (Var varTy name2)) tyS boxTy varTy
    where s = nullSpanNoFile

makeUnboxP :: Id -> Expr () Type -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makeUnboxP name1 expr (Forall _ _ _ goalTy) boxTy varTy e  =
  App s goalTy False
  (Val s (FunTy Nothing Nothing boxTy goalTy) False
    (Abs (FunTy Nothing Nothing boxTy goalTy)
      (PBox s boxTy False
        (PVar s varTy False name1)) (Just boxTy) e))
  expr
    where s = nullSpanNoFile

makeUnboxUntyped :: Id -> Expr () () -> Expr () () -> Expr () ()
makeUnboxUntyped name1 expr e =
  App s () False
  (Val s () False
    (Abs ()
      (PBox s () False
        (PVar s () False name1)) Nothing e))
  expr
    where s = nullSpanNoFile

makePair :: Type -> Type -> Expr () Type -> Expr () Type -> Expr () Type
makePair lTy rTy e1 e2 =
  App s rTy False (App s lTy False (Val s (ProdTy lTy rTy) False (Constr (ProdTy lTy rTy) (mkId ",") [])) e1) e2
  where s = nullSpanNoFile

makePairUntyped :: Expr () () -> Expr () () -> Expr () ()
makePairUntyped e1 e2 =
  App s () False (App s () False (Val s () False (Constr () (mkId ",") [])) e1) e2
  where s = nullSpanNoFile

makePairElim :: Id -> Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makePairElim name lId rId goalTyS lTy rTy e =
   makePairElimP id (Val s (ProdTy lTy rTy) False (Var (ProdTy lTy rTy) name)) lId rId goalTyS lTy rTy e
     where s = nullSpanNoFile

makePairElimP :: (Pattern Type -> Pattern Type) -> Expr () Type -> Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type -> Expr () Type
makePairElimP ptransf elimExpr lId rId (Forall _ _ _ goalTy) lTy rTy e =
  App s goalTy False
  (Val s (ProdTy lTy rTy) False
    (Abs (FunTy Nothing Nothing (ProdTy lTy rTy) goalTy)
      (ptransf $ PConstr s (ProdTy lTy rTy) False (mkId ",") [(PVar s lTy False lId), (PVar s rTy False rId)] )
        Nothing e)) elimExpr
  where s = nullSpanNoFile

makePairElimPUntyped :: (Pattern () -> Pattern ()) -> Expr () () -> Id -> Id -> Expr () () -> Expr () ()
makePairElimPUntyped ptransf elimExpr lId rId e =
  App s () False
  (Val s () False
    (Abs ()
      (ptransf $ PConstr s () False (mkId ",") [(PVar s () False lId), (PVar s () False rId)] )
        Nothing e)) elimExpr
  where s = nullSpanNoFile

makePairElimPUntyped' :: (Pattern () -> Pattern ()) -> Expr () () -> Id -> Id -> Expr () () -> Expr () ()
makePairElimPUntyped' ptransf elimExpr lId rId e =
  App s () False
  (Val s () False
    (Abs ()
      (PConstr s () False (mkId ",") [ptransf (PVar s () False lId), ptransf  (PVar s () False rId)] )
        Nothing e)) elimExpr
  where s = nullSpanNoFile

makeEitherLeft :: Type -> Type -> Expr () Type -> Expr () Type
makeEitherLeft lTy rTy e  =
  (App s lTy False (Val s (SumTy lTy rTy) False (Constr (SumTy lTy rTy) (mkId "Left") [])) e)
  where s = nullSpanNoFile

makeEitherRight :: Type -> Type -> Expr () Type -> Expr () Type
makeEitherRight lTy rTy e  =
  (App s rTy False (Val s (SumTy lTy rTy) False (Constr (SumTy lTy rTy) (mkId "Right") [])) e)
  where s = nullSpanNoFile

-- makeCase :: Type -> Type -> Id -> Id -> Id -> Expr () Type -> Expr () Type -> Expr () Type
-- makeCase t1 t2 sId lId rId lExpr rExpr =
--    Case s (SumTy t1 t2) False (Val s (SumTy t1 t2) False (Var (SumTy t1 t2) sId)) [(PConstr s (SumTy t1 t2) False (mkId "Left") [(PVar s t1 False lId)], lExpr), (PConstr s (SumTy t1 t2) False (mkId "Right") [(PVar s t2 False rId)], rExpr)]
--  where s = nullSpanNoFile

makeCase :: Type -> Id -> [(Pattern Type, Expr () Type)] -> Type -> Maybe Type -> Expr () Type
makeCase ty id exprPats goal grade = 
  case grade of
    Nothing     -> Case s goal False (Val s ty False (Var ty id)) exprPats
    Just grade' -> Case s goal False  (Val s (Box ty grade') False (Promote (Box ty grade') (Val s ty False (Var ty id)))) exprPats
  where s = nullSpanNoFile 

makeBoxCase :: Type -> Type -> Id -> [(Pattern Type, Expr () Type)] -> Type -> Expr () Type
makeBoxCase ty grade id exprPats goal = 
  Case s goal False (Val s (Box ty grade) False (Promote (Box ty grade) (Val s ty False (Var ty id)))) exprPats
  where s = nullSpanNoFile 

makeNullaryConstructor :: Id -> Expr () Type
makeNullaryConstructor id =
  Val nullSpanNoFile (TyCon id) True
    (Constr (TyCon id) id [])

makeConstr :: [((Expr () Type), Type)] -> Id -> Type -> Expr () Type
makeConstr terms name goal = buildTerm (reverse terms)
  where s = nullSpanNoFile
        buildTerm [] = Val s goal False (Constr goal name [])
        buildTerm ((e, ty):es) =
          let e' = buildTerm es in
            App s ty False e' e

makeUnitElim :: Id -> Expr () Type -> TypeScheme -> Expr () Type
makeUnitElim name e tyS = makeUnitElimP id
    (Val s (TyCon (Id "()" "()")) False (Var (TyCon (Id "()" "()")) name)) e tyS
  where s = nullSpanNoFile

makeUnitElimP :: (Pattern Type -> Pattern Type) -> Expr () Type -> Expr () Type -> TypeScheme -> Expr () Type
makeUnitElimP patTransf argExpr e (Forall _ _ _ goalTy) =
  Case s goalTy False argExpr
    [((patTransf (PConstr s (TyCon (Id "()" "()")) False (mkId "()") [])), e)]
  where s = nullSpanNoFile

makeUnitElimPUntyped :: (Pattern () -> Pattern ()) -> Expr () () -> Expr () () -> Expr () ()
makeUnitElimPUntyped patTransf argExpr e =
  Case s () False argExpr
    [((patTransf (PConstr s () False (mkId "()") [])), e)]
  where s = nullSpanNoFile

makeUnitIntro :: Expr () Type
makeUnitIntro =
  Val nullSpanNoFile (TyCon (mkId "()")) True
    (Constr (TyCon (mkId "()")) (mkId "()") [])

makeUnitIntroUntyped :: Expr () ()
makeUnitIntroUntyped =
  Val nullSpanNoFile () True (Constr () (mkId "()") [])

--makeEitherCase :: Id -> Id -> Id -> TypeScheme -> Type -> Type -> Expr () Type
--makeEitherCase name lId rId (Forall _ _ _ goalTy) lTy rTy =
