{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Expr where

import Data.List
import Control.Monad.State.Strict

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

data Expr = Abs Id Expr
          | App Expr Expr
          | Var Id
          | Num Int
          | Binop Op Expr Expr
          | Promote Expr
          | LetBox Id Type Expr Expr
          | Pure Expr
          | LetDiamond Id Type Expr Expr
          deriving (Eq, Show)


fvs :: Expr -> [Id]
fvs (Abs x e) = (fvs e) \\ [x]
fvs (App e1 e2) = fvs e1 ++ fvs e2
fvs (Var x)   = [x]
fvs (Binop _ e1 e2) = fvs e1 ++ fvs e2
fvs (Promote e) = fvs e
fvs (LetBox x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
fvs (Pure e) = fvs e
fvs (LetDiamond x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
fvs _ = []

-- Syntactic substitution (assuming variables are all unique)
subst :: Expr -> Id -> Expr -> Expr
subst es v (Abs w e)          = Abs w (subst es v e)
subst es v (App e1 e2)        = App (subst es v e1) (subst es v e2)
subst es v (Binop op e1 e2)   = Binop op (subst es v e1) (subst es v e2)
subst es v (Promote e)        = Promote (subst es v e)
subst es v (LetBox w t e1 e2) = LetBox w t (subst es v e1) (subst es v e2)
subst es v (Pure e)           = Pure (subst es v e)
subst es v (LetDiamond w t e1 e2) = LetDiamond w t (subst es v e1) (subst es v e2)
subst es v (Var w) | v == w = es
subst es v e = e

--------- Definitions5

type Pattern = Either String String

data Def = Def Id Expr [Pattern] Type
          deriving (Eq, Show)

desugar :: Def -> Def
desugar (Def id e pats ty) =
  Def id (evalState (desguarPats e pats ty []) 0) [] ty
  where
    unfoldBoxes [] e = e
    unfoldBoxes ((v, v', t) : binds) e =
      LetBox v t (Var v') (unfoldBoxes binds e)

    desguarPats e [] _ boxed =
      return $ unfoldBoxes boxed e

    desguarPats e (Left v : pats) (FunTy _ t2) boxed = do
      e' <- desguarPats e pats t2 boxed
      return $ Abs v e'

    desguarPats e (Right v : pats) (FunTy (Box _ t) t2) boxed = do
      n <- get
      let v' = v ++ show n
      put (n + 1)
      e' <- desguarPats e pats t2 (boxed ++ [(v, v', t)])
      return $ Abs v' e'

    desguarPats e _ _ _ = error $ "Definition of " ++ id ++ "expects at least " ++
                      show (length pats) ++ " arguments, but signature " ++
                      " specifies: " ++ show (arity ty)

----------- Types

data TyCon = TyInt | TyBool | TyVar String -- TyVar not used yet
    deriving (Eq, Show)

data Type = FunTy Type Type | ConT TyCon | Box Coeffect Type | Diamond Effect Type
    deriving (Eq, Show)

arity (FunTy _ t) = 1 + arity t
arity _           = 0

type Effect = [String]

data Coeffect = Nat Int
              | CVar String
              | CPlus Coeffect Coeffect
              | CTimes Coeffect Coeffect
    deriving (Eq, Show)

{- Pretty printers -}

class Pretty t where
    pretty :: t -> String

instance Pretty Coeffect where
    pretty (Nat n) = show n
    pretty (CVar c) = c
    pretty (CPlus c d) = pretty c ++ " + " ++ pretty d
    pretty (CTimes c d) = pretty c ++ " * " ++ pretty d

instance Pretty Type where
    pretty (ConT TyInt)  = "Int"
    pretty (ConT TyBool) = "Bool"
    pretty (FunTy t1 t2) = "(" ++ pretty t1 ++ ") -> " ++ pretty t2
    pretty (Box c t) = "|" ++ pretty t ++ "| " ++ pretty c
    pretty (Diamond e t) = "<" ++ pretty t ++ "> {" ++ (intercalate "," e) ++ "}"

instance Pretty [Def] where
    pretty = intercalate "\n"
     . map (\(Def v e ps t) -> v ++ " : " ++ pretty t ++ "\n"
                                ++ v ++ pretty ps ++ " = " ++ pretty e)

instance Pretty [Either String String] where
    pretty ps = intercalate " " (map pretty' ps)
      where
        pretty' (Left v) = v
        pretty' (Right v) = "|" ++ v ++ "|"

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

{-
instance Pretty t => Pretty [t] where
    pretty ts = "|" ++ (intercalate "," $ map pretty ts) ++ "|"
-}

instance Pretty Expr where
    pretty expr =
      case expr of
        (Abs x e) -> parens $ "\\" ++ x ++ " -> " ++ pretty e
        (App e1 e2) -> parens $ pretty e1 ++ " " ++ pretty e2
        (Binop op e1 e2) -> parens $ pretty e1 ++ prettyOp op ++ pretty e2
        (LetBox v t e1 e2) -> parens $ "let [" ++ v ++ ":" ++ pretty t ++ "] = "
                                     ++ pretty e1 ++ " in " ++ pretty e2
        (Promote e)      -> "[ " ++ pretty e ++ " ]"
        (Pure e)         -> "<" ++ pretty e ++ ">"
        (LetDiamond v t e1 e2) -> parens $ "let <" ++ v ++ ":" ++ pretty t ++ "> = "
                                     ++ pretty e1 ++ " in " ++ pretty e2
        (Var x) -> x
        (Num n) -> show n
     where prettyOp Add = " + "
           prettyOp Sub = " - "
           prettyOp Mul = " * "
           parens s = "(" ++ s ++ ")"

{- Smart constructors -}

addExpr :: Expr -> Expr -> Expr
addExpr = Binop Add

subExpr :: Expr -> Expr -> Expr
subExpr = Binop Sub

mulExpr :: Expr -> Expr -> Expr
mulExpr = Binop Mul

uniqueNames :: [Def] -> ([Def], [(Id, Id)])
uniqueNames = flip evalState (0 :: Int) . mapFoldMSnd uniqueNameDef
  where
    mapFoldMSnd :: Monad m => (a -> m (b, [c])) -> [a] -> m ([b], [c])
    mapFoldMSnd f xs = foldM (composer f) ([], []) xs
      where composer f (bs, cs) a = do
              (b, cs') <- f a
              return (bs ++ [b], cs ++ cs')

    uniqueNameDef (Def id e ps t) = do
      (e', rs)   <- uniqueNameExpr e
      (ps', rs') <- mapFoldMSnd uniqueNamePat ps
      return $ (Def id e' ps' t, rs ++ rs')

    freshen id = do
      v <- get
      let id' = id ++ show v
      put (v+1)
      return id'

    -- TODO: convert renaming map to be build in the WriterT monad
    uniqueNamePat (Left id) = do
      id' <- freshen id
      return $ (Left id', [(id', id)])

    uniqueNamePat (Right id) = do
      id' <- freshen id
      return $ (Right id', [(id',  id)])

    uniqueNameExpr (Abs id e) = do
      id' <- freshen id
      (e', rs) <- uniqueNameExpr (subst (Var id') id e)
      return $ (Abs id' e', (id', id) : rs)

    uniqueNameExpr (LetBox id t e1 e2) = do
      id' <- freshen id
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr (subst (Var id') id e2)
      return $ (LetBox id' t e1' e2', (id', id) : (rs1 ++ rs2))

    uniqueNameExpr (App e1 e2) = do
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr e2
      return $ (App e1' e2', rs1 ++ rs2)

    uniqueNameExpr (LetDiamond id t e1 e2) = do
      id' <- freshen id
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr (subst (Var id') id e2)
      return $ (LetDiamond id' t e1' e2', (id', id) : rs1 ++ rs2)

    uniqueNameExpr (Pure e) = do
      (e', rs) <- uniqueNameExpr e
      return $ (Pure e', rs)

    uniqueNameExpr (Binop op e1 e2) = do
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr e2
      return $ (Binop op e1' e2', rs1 ++ rs2)

    uniqueNameExpr (Promote e) = do
      (e', rs) <- uniqueNameExpr e
      return $ (Promote e', rs)

    uniqueNameExpr c = return (c, [])

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
