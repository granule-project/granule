-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module Syntax.Pretty where

import Data.List
import Syntax.Expr
import Utils

-- The pretty printer class
class Pretty t where
    pretty :: (?globals :: Globals) => t -> String

-- Mostly for debugging

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b) => Pretty (a, b) where
   pretty (a, b) = "(" ++ pretty a ++ ", " ++ pretty b ++ ")"

instance {-# OVERLAPS #-} Pretty String where
   pretty s = s

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
   pretty xs = "[" ++ intercalate "," (map pretty xs) ++ "]"

-- Core pretty printers

instance {-# OVERLAPS #-} Pretty Effect where
   pretty es = "[" ++ intercalate "," es ++ "]"

instance Pretty Coeffect where
    pretty (CNat Ordered n) = show n
    pretty (CNat Discrete n) = show n ++ "="
    pretty (CNatOmega (Left ())) = "∞"
    pretty (CNatOmega (Right x)) = show x
    pretty (CFloat n) = show n
    pretty (COne k)  = "_1 : " ++ pretty k
    pretty (CZero k) = "_0 : " ++ pretty k
    pretty (Level 0) = "Public"
    pretty (Level _) = "Private"
    pretty (CVar c) = pretty c
    pretty (CMeet c d) =
      pretty c ++ " /\\ " ++ pretty d
    pretty (CJoin c d) =
      pretty c ++ " \\/ " ++ pretty d
    pretty (CPlus c d) =
      pretty c ++ " + " ++ pretty d
    pretty (CTimes c d) =
      pretty c ++ " * " ++ pretty d
    pretty (CSet xs) =
      "{" ++ intercalate "," (map (\(name, t) -> name ++ " : " ++ pretty t) xs) ++ "}"
    pretty (CSig c t) = "(" ++ pretty c ++ " : " ++ pretty t ++ ")"
    pretty (CInfinity (CPoly kv)) | internalName kv == "infinity" = "∞"
    pretty (CInfinity k) = "∞ : " ++ pretty k

instance Pretty Kind where
    pretty KType          = "Type"
    pretty KCoeffect      = "Coeffect"
    pretty (KFun k1 k2)   = pretty k1 ++ " -> " ++ pretty k2
    pretty (KConstr c)    = pretty c
    pretty (KVar v)      = pretty v

instance Pretty TypeScheme where
    pretty (Forall _ [] t) = pretty t
    pretty (Forall _ cvs t) =
        "forall " ++ intercalate ", " (map prettyKindSignatures cvs) ++ ". " ++ pretty t
      where
       prettyKindSignatures (var, kind) = pretty var ++ " : " ++ pretty kind

instance Pretty CKind where
    pretty (CConstr c) = pretty c
    pretty (CPoly   v) = pretty v

instance Pretty Type where
    pretty (TyCon s)      =  pretty s
    pretty (FunTy t1 t2)  = "(" ++ pretty t1 ++ ") -> " ++ pretty t2
    pretty (Box c t)      = "(" ++ pretty t ++ ") |" ++ pretty c ++ "|"
    pretty (Diamond e t)  = "(" ++ pretty t ++ ") <[" ++ intercalate "," e ++ "]>"
    pretty (TyVar v)      = pretty v
    pretty (TyApp t1 t2)  = pretty t1 ++ " " ++ pretty t2
    pretty (TyInt n)      = show n
    pretty (PairTy t1 t2) = "(" ++ pretty t1 ++ "," ++ pretty t2 ++ ")"
    pretty (TyInfix op t1 t2) = pretty t1 ++ " " ++ op ++ " " ++  pretty t2

instance Pretty AST where
    pretty (AST dataDecls defs) = pretty' dataDecls ++ "\n\n" ++ pretty' defs
      where
        pretty' :: Pretty a => [a] -> String
        pretty' = intercalate "\n\n" . map pretty

instance Pretty Def where
    pretty (Def _ v e ps t) = pretty v ++ " : " ++ pretty t ++ "\n" ++
                              pretty v ++ " " ++ pretty ps ++ "= " ++ pretty e

instance Pretty DataDecl where
    pretty (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> (unwords . map pretty) tyVars ++ " "
          ki = case kind of Nothing -> ""; Just k -> pretty k ++ " "
      in "data " ++ pretty tyCon ++ " " ++ tvs ++ ki ++ "where\n  " ++ pretty dataConstrs

instance Pretty [DataConstr] where
    pretty = intercalate ";\n  " . map pretty

instance Pretty DataConstr where
    pretty (DataConstr _ name typeScheme) = pretty name ++ " : " ++ pretty typeScheme

instance Pretty Pattern where
    pretty (PVar _ v)     = pretty v
    pretty (PWild _)      = "_"
    pretty (PBox _ p)     = "|" ++ pretty p ++ "|"
    pretty (PInt _ n)     = show n
    pretty (PFloat _ n)   = show n
    pretty (PPair _ p1 p2) = "(" ++ pretty p1 ++ "," ++ pretty p2 ++ ")"
    pretty (PConstr _ name args)  = intercalate " " (pretty name : map pretty args)

instance {-# OVERLAPS #-} Pretty [Pattern] where
    pretty [] = ""
    pretty ps = unwords (map pretty ps) ++ " "

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty Value where
    pretty (Abs x t e)  = parens $ "\\(" ++ pretty x ++ " : " ++ pretty t
                               ++ ") -> " ++ pretty e
    pretty (Promote e)  = "|" ++ pretty e ++ "|"
    pretty (Pure e)     = "<" ++ pretty e ++ ">"
    pretty (Var x)      = pretty x
    pretty (NumInt n)   = show n
    pretty (NumFloat n) = show n
    pretty (CharLiteral c) = show c
    pretty (StringLiteral s) = show s
    pretty (Pair e1 e2) = "(" ++ pretty e1 ++ "," ++ pretty e2 ++ ")"
    pretty (Constr s vs) = intercalate " " (pretty s : map (parensOn (not . valueAtom)) vs)
      where
        -- Syntactically atomic values
        valueAtom (NumInt _)    = True
        valueAtom (NumFloat _)  = True
        valueAtom (Constr _ []) = True
        valueAtom _             = False

instance Pretty Id where
  pretty = if debugging ?globals then internalName else sourceName

instance Pretty Expr where
  pretty (App _ e1 e2) = parens $ pretty e1 ++ " " ++ pretty e2
  pretty (Binop _ op e1 e2) = parens $ pretty e1 ++ " " ++ op ++ " " ++ pretty e2
  pretty (LetDiamond _ v t e1 e2) = parens $ "let " ++ pretty v ++ " :" ++ pretty t ++ " <- "
                                    ++ pretty e1 ++ " in " ++ pretty e2
  pretty (Val _ v) = pretty v
  pretty (Case _ e ps) = "\n    (case " ++ pretty e ++ " of\n      " ++
                         intercalate ";\n      " (map (\(p, e') -> pretty p ++ " -> " ++ pretty e') ps) ++ ")"

parens :: String -> String
parens s = "(" ++ s ++ ")"

parensOn :: (?globals :: Globals) => Pretty a => (a -> Bool) -> a -> String
parensOn p t =
  if p t
    then "(" ++ pretty t ++ ")"
    else pretty t

instance Pretty Int where
  pretty = show
