-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Syntax.Pretty where

import Data.List
import Syntax.Expr

-- The pretty printer class
class Pretty t where
    pretty :: t -> String

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
    pretty (Level 0) = "Lo"
    pretty (Level _) = "Hi"
    pretty (CVar c) = c
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
    pretty (CInfinity k) = "∞ : " ++ pretty k

instance Pretty Kind where
    pretty KType          = "Type"
    pretty KCoeffect      = "Coeffect"
    pretty (KFun k1 k2)   = pretty k1 ++ " -> " ++ pretty k2
    pretty (KConstr c)    = c
    pretty (KPoly v)      = v

instance Pretty TypeScheme where
    pretty (Forall _ cvs t) =
      "forall " ++ intercalate ", " (map prettyKindSignatures cvs)
                ++ ". " ++ pretty t
      where
       prettyKindSignatures (var, kind) = var ++ " : " ++ pretty kind

instance Pretty CKind where
    pretty (CConstr c) = c
    pretty (CPoly   v) = v

instance Pretty Type where
    pretty (TyCon s)       = s
    pretty (FunTy t1 t2)  = "(" ++ pretty t1 ++ ") -> " ++ pretty t2
    pretty (Box c t)      = pretty t ++ " |" ++ pretty c ++ "|"
    pretty (Diamond e t)  = pretty t ++ " <[" ++ intercalate "," e ++ "]>"
    pretty (TyVar v)      = v
    pretty (TyApp t1 t2)  = pretty t1 ++ " " ++ pretty t2
    pretty (TyInt n)      = show n
    pretty (PairTy t1 t2) = "(" ++ pretty t1 ++ "," ++ pretty t2 ++ ")"
    pretty (TyInfix op t1 t2) = pretty t1 ++ " " ++ op ++ " " ++  pretty t2

instance {-# OVERLAPS #-} Pretty [Def] where
    pretty = intercalate "\n\n" . map pretty

instance Pretty Def where
    pretty (Def _ v e ps t) = v ++ " : " ++ pretty t ++ "\n"
                                ++ v ++ " " ++ pretty ps ++ "= " ++ pretty e
    pretty (ADT _ tC dCs) = "data " ++ pretty tC ++ " where\n  " ++ pretty dCs

instance Pretty TypeConstr where
    pretty tC = _name (tC :: TypeConstr) ++ " " ++ (unwords $ map snd $ _tyVars tC)

instance Pretty [DataConstr] where
    pretty = intercalate "\n  " . map pretty

instance Pretty DataConstr where
    pretty dC = _name (dC :: DataConstr) ++ " : " ++ pretty (_signature dC)

instance Pretty Pattern where
    pretty (PVar _ v)     = v
    pretty (PWild _)      = "_"
    pretty (PBox _ p)     = "|" ++ pretty p ++ "|"
    pretty (PInt _ n)     = show n
    pretty (PFloat _ n)   = show n
    pretty (PApp _ p1 p2) = pretty p1 ++ " " ++ pretty p2
    pretty (PConstr _ s)  = s
    pretty (PPair _ p1 p2) = "(" ++ pretty p1 ++ "," ++ pretty p2 ++ ")"

instance {-# OVERLAPS #-} Pretty [Pattern] where
    pretty ps = unwords (map pretty ps)

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty Value where
    pretty (Abs x t e)  = parens $ "\\" ++ x ++ " : " ++ pretty t
                               ++ " -> " ++ pretty e
    pretty (Promote e)  = "|" ++ pretty e ++ "|"
    pretty (Pure e)     = "<" ++ pretty e ++ ">"
    pretty (Var x)      = x
    pretty (NumInt n)   = show n
    pretty (NumFloat n) = show n
    pretty (Pair e1 e2) = "(" ++ pretty e1 ++ "," ++ pretty e2 ++ ")"
    pretty (Constr s vs) = intercalate " " (s : map (parensOn (not . valueAtom)) vs)
      where
        -- Syntactically atomic values
        valueAtom (NumInt _)    = True
        valueAtom (NumFloat _)  = True
        valueAtom (Constr _ []) = True
        valueAtom _             = False

instance Pretty Expr where
  pretty (App _ e1 e2) = parens $ pretty e1 ++ " " ++ pretty e2
  pretty (Binop _ op e1 e2) = parens $ pretty e1 ++ " " ++ op ++ " " ++ pretty e2
  pretty (LetBox _ v t e1 e2) = parens $ "let |" ++ v ++ "| :" ++ pretty t ++ " = "
                                ++ pretty e1 ++ " in " ++ pretty e2
  pretty (LetDiamond _ v t e1 e2) = parens $ "let " ++ v ++ " :" ++ pretty t ++ " <- "
                                    ++ pretty e1 ++ " in " ++ pretty e2
  pretty (Val _ v) = pretty v
  pretty (Case _ e ps) = "case " ++ pretty e ++ " of " ++
                         intercalate ";" (map (\(p, e') -> pretty p ++ " -> " ++ pretty e') ps)

parens :: String -> String
parens s = "(" ++ s ++ ")"

parensOn :: Pretty a => (a -> Bool) -> a -> String
parensOn p t =
  if p t
    then "(" ++ pretty t ++ ")"
    else pretty t

instance Pretty Int where
  pretty = show
