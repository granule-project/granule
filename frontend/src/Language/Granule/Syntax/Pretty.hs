-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Pretty where

import Data.List
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils

prettyDebug :: (?globals :: Globals) => Pretty t => t -> String
prettyDebug x =
  let ?globals = ?globals { debugging = True }
  in pretty x

-- The pretty printer class
class Pretty t where
    pretty :: (?globals :: Globals) => t -> String

-- Mostly for debugging

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b) => Pretty (a, b) where
   pretty (a, b) = "(" <> pretty a <> ", " <> pretty b <> ")"

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b, Pretty c) => Pretty (a, b,c) where
      pretty (a, b, c) = "(" <> pretty a <> ", " <> pretty b <> "," <> pretty c <> ")"


instance {-# OVERLAPS #-} Pretty String where
   pretty s = s

instance Pretty () where
   pretty () = ""

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
   pretty xs = "[" <> intercalate "," (map pretty xs) <> "]"

-- Core pretty printers

instance {-# OVERLAPS #-} Pretty Effect where
   pretty es = "[" <> intercalate "," es <> "]"

instance Pretty Coeffect where
    pretty (CNat n) = show n
    pretty (CFloat n) = show n
    pretty (COne k)  = "_1 : " <> pretty k
    pretty (CZero k) = "_0 : " <> pretty k
    pretty (Level 0) = "Public"
    pretty (Level _) = "Private"
    pretty (CExpon a b) = pretty a <> "^" <> pretty b
    pretty (CVar c) = pretty c
    pretty (CMeet c d) =
      pretty c <> " /\\ " <> pretty d
    pretty (CJoin c d) =
      pretty c <> " \\/ " <> pretty d
    pretty (CPlus c d) =
      pretty c <> " + " <> pretty d
    pretty (CTimes c d) =
      pretty c <> " * " <> pretty d
    pretty (CSet xs) =
      "{" <> intercalate "," (map (\(name, t) -> name <> " : " <> pretty t) xs) <> "}"
    pretty (CSig c t) = "(" <> pretty c <> " : " <> pretty t <> ")"
    pretty (CInfinity k) = "∞ : " <> pretty k
    pretty (CInterval c1 c2) = pretty c1 <> ".." <> pretty c2

instance Pretty Kind where
    pretty KType          = "Type"
    pretty KCoeffect      = "Coeffect"
    pretty (KFun k1 k2)   = pretty k1 <> " -> " <> pretty k2
    pretty (KConstr c)    = pretty c
    pretty (KVar v)       = pretty v
    pretty (KPromote t)   = "↑" <> pretty t

instance Pretty TypeScheme where
    pretty (Forall _ [] t) = pretty t
    pretty (Forall _ cvs t) =
        "forall " <> intercalate ", " (map prettyKindSignatures cvs) <> ". " <> pretty t
      where
       prettyKindSignatures (var, kind) = pretty var <> " : " <> pretty kind

instance Pretty Type where
    pretty (TyCon s)      =  pretty s
    pretty (FunTy f@(FunTy _ _) t2)  = "(" <> pretty f <> ") -> " <> pretty t2
    pretty (FunTy t1 t2)  = pretty t1 <> " -> " <> pretty t2
    pretty (Box c t)      = "((" <> pretty t <> ") |" <> pretty c <> "|)"
    pretty (Diamond e t)  = "((" <> pretty t <> ") <" <> pretty e <> ">)"
    pretty (TyVar v)      = pretty v
    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "," =
      "(" <> pretty t1 <> ", " <> pretty t2 <> ")"
    pretty (TyApp t1 t2)  = pretty t1 <> " " <> pretty t2
    pretty (TyInt n)      = show n
    pretty (TyInfix op t1 t2) = "(" <> pretty t1 <> " " <> op <> " " <>  pretty t2 <> ")"

instance Pretty (Value v a) => Pretty (AST v a) where
    pretty (AST dataDecls defs) = pretty' dataDecls <> "\n\n" <> pretty' defs
      where
        pretty' :: Pretty l => [l] -> String
        pretty' = intercalate "\n\n" . map pretty

instance Pretty (Value v a) => Pretty (Def v a) where
    pretty (Def _ v e ps t) = pretty v <> " : " <> pretty t <> "\n" <>
                              pretty v <> " " <> pretty ps <> "= " <> pretty e

instance Pretty DataDecl where
    pretty (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> (unwords . map pretty) tyVars <> " "
          ki = case kind of Nothing -> ""; Just k -> pretty k <> " "
      in "data " <> pretty tyCon <> " " <> tvs <> ki <> "where\n  " <> pretty dataConstrs

instance Pretty [DataConstr] where
    pretty = intercalate ";\n  " . map pretty

instance Pretty DataConstr where
    pretty (DataConstrG _ name typeScheme) = pretty name <> " : " <> pretty typeScheme
    pretty (DataConstrA _ name params) = pretty name <> (unwords . map pretty) params

instance Pretty (Pattern a) where
    pretty (PVar _ _ v)     = pretty v
    pretty (PWild _ _)      = "_"
    pretty (PBox _ _ p)     = "|" <> pretty p <> "|"
    pretty (PInt _ _ n)     = show n
    pretty (PFloat _ _ n)   = show n
    pretty (PConstr _ _ name args)  = intercalate " " (pretty name : map pretty args)

instance {-# OVERLAPS #-} Pretty [Pattern a] where
    pretty [] = ""
    pretty ps = unwords (map pretty ps) <> " "

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty v => Pretty (Value v a) where
    pretty (Abs _ x t e)  = parens $ "\\(" <> pretty x <> " : " <> pretty t
                               <> ") -> " <> pretty e
    pretty (Promote _ e)  = "|" <> pretty e <> "|"
    pretty (Pure _ e)     = "<" <> pretty e <> ">"
    pretty (Var _ x)      = pretty x
    pretty (NumInt n)   = show n
    pretty (NumFloat n) = show n
    pretty (CharLiteral c) = show c
    pretty (StringLiteral s) = show s
    pretty (Constr _ s vs) | internalName s == "," =
      "(" <> intercalate ", " (map pretty vs) <> ")"
    pretty (Constr _ s vs) = intercalate " " (pretty s : map (parensOn (not . valueAtom)) vs)
      where
        -- Syntactically atomic values
        valueAtom (NumInt _)    = True
        valueAtom (NumFloat _)  = True
        valueAtom (Constr _ _ []) = True
        valueAtom _             = False
    pretty (Ext _ _) = ""

instance Pretty Id where
  pretty = if debugging ?globals then internalName else sourceName

instance Pretty (Value v a) => Pretty (Expr v a) where
  pretty (App _ _ e1 e2) = parens $ pretty e1 <> " " <> pretty e2
  pretty (Binop _ _ op e1 e2) = parens $ pretty e1 <> " " <> op <> " " <> pretty e2
  pretty (LetDiamond _ _ v t e1 e2) = parens $ "let " <> pretty v <> " :" <> pretty t <> " <- "
                                    <> pretty e1 <> " in " <> pretty e2
  pretty (Val _ _ v) = pretty v
  pretty (Case _ _ e ps) = "\n    (case " <> pretty e <> " of\n      " <>
                         intercalate ";\n      " (map (\(p, e') -> pretty p <> " -> " <> pretty e') ps) <> ")"

parens :: String -> String
parens s = "(" <> s <> ")"

parensOn :: (?globals :: Globals) => Pretty a => (a -> Bool) -> a -> String
parensOn p t =
  if p t
    then "(" <> pretty t <> ")"
    else pretty t

instance Pretty Int where
  pretty = show
