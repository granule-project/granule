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
    pretty (Nat n) = show n
    pretty (Level 0) = "Lo"
    pretty (Level n) = "Hi"
    pretty (CVar c) = c
    pretty (CPlus c d) =
      case (kindOf c `kindJoin` kindOf d) of
        CLevel -> pretty c ++ " \\/ " ++ pretty d
        _      -> pretty c ++ " + " ++ pretty d
    pretty (CTimes c d) =
      case (kindOf c `kindJoin` kindOf d) of
        CLevel -> pretty c ++ " /\\ " ++ pretty d
        _      -> pretty c ++ " * " ++ pretty d

instance Pretty Type where
    pretty (ConT TyInt)  = "Int"
    pretty (ConT TyBool) = "Bool"
    pretty (FunTy t1 t2) = "(" ++ pretty t1 ++ ") -> " ++ pretty t2
    pretty (Box c t) = "|" ++ pretty t ++ "| " ++ pretty c
    pretty (Diamond e t) = "<" ++ pretty t ++ "> [" ++ (intercalate "," e) ++ "]"

instance Pretty [Def] where
    pretty = intercalate "\n"
     . map (\(Def v e ps t) -> v ++ " : " ++ pretty t ++ "\n"
                                ++ v ++ pretty ps ++ " = " ++ pretty e)

instance Pretty [Pattern] where
    pretty ps = intercalate " " (map pretty' ps)
      where
        pretty' (PVar v)    = v
        pretty' (PBoxVar v) = "|" ++ v ++ "|"
        pretty' PWild       = "_"

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty Value where
    pretty (Abs x e)   = parens $ "\\" ++ x ++ " -> " ++ pretty e
    pretty (Promote e) = "[ " ++ pretty e ++ " ]"
    pretty (Pure e)    = "<" ++ pretty e ++ ">"
    pretty (Var x)     = x
    pretty (Num n)     = show n


instance Pretty Expr where
    pretty expr =
      case expr of
        (App e1 e2) -> parens $ pretty e1 ++ " " ++ pretty e2
        (Binop op e1 e2) -> parens $ pretty e1 ++ prettyOp op ++ pretty e2
        (LetBox v t e1 e2) -> parens $ "let [" ++ v ++ ":" ++ pretty t ++ "] = "
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
