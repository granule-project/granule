-- Pretty printer for Gram
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Syntax.Pretty where

import Data.List
import Syntax.Expr

-- The pretty printer class
class Pretty t where
    pretty :: t -> String

instance Pretty Effect where
   pretty es = "[" ++ intercalate "," es ++ "]"

instance Pretty Coeffect where
    pretty (CNat n) = show n
    pretty (CNatOmega (Left ())) = "*"
    pretty (CNatOmega (Right x)) = show x
    pretty (CReal n) = show n
    pretty (COne)    = "_1"
    pretty (CZero)   = "_0"
    pretty (Level 0) = "Lo"
    pretty (Level n) = "Hi"
    pretty (CVar c) = c
    pretty (CPlus c d) =
      pretty c ++ " + " ++ pretty d
    pretty (CTimes c d) =
      pretty c ++ " * " ++ pretty d

instance Pretty TypeScheme where
    pretty (Forall cvs t) =
      "forall " ++ intercalate "," (map prettyKindSignatures cvs)
                ++ " . " ++ pretty t
      where
       prettyKindSignatures (var, CPoly "") = var
       prettyKindSignatures (var, ckind)    = var ++ " : " ++ pretty ckind

instance Pretty CKind where
    pretty (CConstr c) = c
    pretty (CPoly   v) = v

instance Pretty Type where
    pretty (ConT s)  = s
    pretty (FunTy t1 t2) = "(" ++ pretty t1 ++ ") -> " ++ pretty t2
    pretty (Box c t) = "|" ++ pretty t ++ "| " ++ pretty c
    pretty (Diamond e t) = "<" ++ pretty t ++ "> [" ++ (intercalate "," e) ++ "]"
    pretty (TyVar v) = v

instance Pretty [Def] where
    pretty = intercalate "\n"
     . map (\(Def v e ps t) -> v ++ " : " ++ pretty t ++ "\n"
                                ++ v ++ pretty ps ++ " = " ++ pretty e)

instance Pretty Pattern where
    pretty (PVar v)    = v
    pretty PWild       = "_"
    pretty (PBoxVar v) = "|" ++ v ++ "|"
    pretty (PInt n)    = show n
    pretty (PReal n)    = show n
    pretty (PApp p1 p2) = show p1 ++ " " ++ show p2
    pretty (PConstr s)  = s

instance Pretty [Pattern] where
    pretty ps = intercalate " " (map pretty ps)

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty Value where
    pretty (Abs x e)   = parens $ "\\" ++ x ++ " -> " ++ pretty e
    pretty (Promote e) = "[ " ++ pretty e ++ " ]"
    pretty (Pure e)    = "<" ++ pretty e ++ ">"
    pretty (Var x)     = x
    pretty (NumInt n)  = show n
    pretty (NumReal n) = show n
    pretty (Constr s)  = s


instance Pretty Expr where
    pretty expr =
      case expr of
        (App e1 e2) -> parens $ pretty e1 ++ " " ++ pretty e2
        (Binop op e1 e2) -> parens $ pretty e1 ++ prettyOp op ++ pretty e2
        (LetBox v t k e1 e2) -> parens $ "let [" ++ v ++ ":" ++ pretty t ++ "]" ++ pretty k ++ " = "
                                     ++ pretty e1 ++ " in " ++ pretty e2
        (LetDiamond v t e1 e2) -> parens $ "let <" ++ v ++ ":" ++ pretty t ++ "> = "
                                     ++ pretty e1 ++ " in " ++ pretty e2
        (Val v) -> pretty v
     where prettyOp Add = " + "
           prettyOp Sub = " - "
           prettyOp Mul = " * "

parens s = "(" ++ s ++ ")"

instance Pretty Int where
  pretty = show
