-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Language.Granule.Syntax.Pretty where

import Data.Foldable (toList)
import Data.List
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils

prettyDebug :: (?globals :: Globals) => Pretty t => t -> String
prettyDebug x =
  let ?globals = ?globals { globalsDebugging = Just True }
  in pretty x

prettyNested :: (?globals :: Globals, Term a, Pretty a) => a -> String
prettyNested e =
  if isLexicallyAtomic e then pretty e else "(" <> pretty e <> ")"

-- infixr 6 <+>
-- (<+>) :: String -> String -> String
-- s1 <+> s2 = s1 <> " " <> s2


-- The pretty printer class
class Pretty t where
    -- `pretty` pretty printers something at nesting level `l`
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

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left a) = pretty a
  pretty (Right b) = pretty b

-- Core pretty printers

instance Pretty Coeffect where
    pretty (CNat n) = show n
    pretty (CFloat n) = show n
    pretty (COne k) | k == TyCon (mkId "Nat") || k == extendedNat = "1"
    pretty (CZero k) | k == TyCon (mkId "Nat") || k == extendedNat = "0"
    pretty (COne k)  = "(1 : " <> pretty k <> ")"
    pretty (CZero k) = "(0 : " <> pretty k <> ")"
    pretty (Level x) = if x == privateRepresentation
                             then "Private"
                             else if x == publicRepresentation
                                  then "Public"
                                  else "Unused"
    pretty (CExpon a b) = prettyNested a <> "^" <> prettyNested b
    pretty (CVar c) = pretty c
    pretty (CMeet c d) =
      prettyNested c <> " /\\ " <> prettyNested d
    pretty (CJoin c d) =
      prettyNested c <> " \\/ " <> prettyNested d
    pretty (CPlus c d) =
      prettyNested c <> " + " <> prettyNested d
    pretty (CTimes c d) =
      prettyNested c <> " * " <> prettyNested d
    pretty (CMinus c d) =
      prettyNested c <> " - " <> prettyNested d
    pretty (CSet xs) =
      "{" <> intercalate "," (map (\(name, t) -> name <> " : " <> prettyNested t) xs) <> "}"
    pretty (CSig c t) =
      prettyNested c <> " : " <> prettyNested t

    pretty (CInfinity (Just k))
       | k == TyCon (mkId "Nat") || k == extendedNat = "∞"

    pretty (CInfinity k) = "(∞ : " <> pretty k <> ")"
    pretty (CInterval c1 c2) = prettyNested c1 <> ".." <> prettyNested c2
    pretty (CProduct c1 c2) = "(" <> pretty c1 <> ", " <> pretty c2 <> ")"

instance Pretty Kind where
    pretty KType          = "Type"
    pretty KEffect      = "Effect"
    pretty KCoeffect      = "Coeffect"
    pretty KPredicate     = "Predicate"
    pretty (KFun k1 k2)   = prettyNested k1 <> " -> " <> pretty k2
    pretty (KVar v)       = pretty v
    pretty (KPromote t)   = "↑" <> prettyNested t
    pretty (KUnion k1 k2) = "(" <> prettyNested k1 <> " ∪ " <> prettyNested k2 <> ")"

instance Pretty TypeScheme where
    pretty (Forall _ vs cs t) = kVars vs <> constraints cs <> pretty t
      where
        kVars [] = ""
        kVars vs = "forall {" <> intercalate ", " (map prettyKindSignatures vs) <> "} . "
        prettyKindSignatures (var, kind) = pretty var <> " : " <> pretty kind
        constraints [] = ""
        constraints cs = "{" <> intercalate ", " (map pretty cs) <> "} =>\n    "

instance Pretty Type where
    -- Atoms
    pretty (TyCon s)      = pretty s
    pretty (TyVar v)      = pretty v
    pretty (TyInt n)      = show n

    -- Non atoms
    pretty (FunTy t1 t2)  =
      case t1 of
        FunTy{} -> "(" <> pretty t1 <> ") -> " <> pretty t2
        _ -> pretty t1 <> " -> " <> pretty t2

    pretty (Box c t)      =
      prettyNested t <> " [" <> pretty c <> "]"

    pretty (Diamond e t) =
      prettyNested t <> " <" <> pretty e <> ">"

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "," =
      "(" <> pretty t1 <> ", " <> pretty t2 <> ")"

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "×" =
      "(" <> pretty t1 <> " × " <> pretty t2 <> ")"

    pretty (TyApp t1 t2)  =
      pretty t1 <> " " <> prettyNested t2

    pretty (TyInfix op t1 t2) =
      prettyNested t1 <> " " <> pretty op <> " " <> prettyNested t2

    pretty (TySet ts) =
      "{" <> intercalate ", " (map pretty ts) <> "}"

instance Pretty TypeOperator where
  pretty = \case
   TyOpLesser          -> "<"
   TyOpLesserEq        -> "≤"
   TyOpGreater         -> ">"
   TyOpGreaterEq       -> "≥"
   TyOpEq              -> "≡"
   TyOpNotEq           -> "≠"
   TyOpPlus            -> "+"
   TyOpTimes           -> "*"
   TyOpMinus           -> "-"
   TyOpExpon           -> "^"
   TyOpMeet            -> "∧"
   TyOpJoin            -> "∨"

instance Pretty v => Pretty (AST v a) where
  pretty (AST dataDecls defs imprts hidden name) =
    -- Module header (if it exists)
    (case name of
        Nothing -> ""
        Just name -> "module "
                  <> pretty name
                  <> " hiding ("
                  <> (intercalate "," (map pretty (toList hidden)))
                  <> ") where\n\n")
    <> (unlines . map ("import " <>) . toList) imprts
    <> "\n\n" <> pretty' dataDecls
    <> "\n\n" <> pretty' defs
    where
      pretty' :: Pretty l => [l] -> String
      pretty' = intercalate "\n\n" . map pretty

instance Pretty v => Pretty (Def v a) where
    pretty (Def _ v eqs (Forall _ [] [] t))
      = pretty v <> " : " <> pretty t <> "\n" <> intercalate "\n" (map (prettyEqn v) eqs)
    pretty (Def _ v eqs tySch)
      = pretty v <> "\n  : " <> pretty tySch <> "\n" <> intercalate "\n" (map (prettyEqn v) eqs)

prettyEqn :: (?globals :: Globals, Pretty v) => Id -> Equation v a -> String
prettyEqn v (Equation _ _ ps e) =
  pretty v <> " " <> pretty ps <> "= " <> pretty e

instance Pretty DataDecl where
    pretty (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> (unwords . map pretty) tyVars <> " "
          ki = case kind of Nothing -> ""; Just k -> pretty k <> " "
      in "data " <> pretty tyCon <> " " <> tvs <> ki <> "where\n  " <> pretty dataConstrs

instance Pretty [DataConstr] where
    pretty = intercalate ";\n  " . map pretty

instance Pretty DataConstr where
    pretty (DataConstrIndexed _ name typeScheme) = pretty name <> " : " <> pretty typeScheme
    pretty (DataConstrNonIndexed _ name params) = pretty name <> (unwords . map pretty) params

instance Pretty (Pattern a) where
    pretty (PVar _ _ v)     = pretty v
    pretty (PWild _ _)      = "_"
    pretty (PBox _ _ p)     = "[" <> pretty p <> "]"
    pretty (PInt _ _ n)     = show n
    pretty (PFloat _ _ n)   = show n
    pretty (PConstr _ _ name args)  = intercalate " " (pretty name : map prettyNested args)

instance {-# OVERLAPS #-} Pretty [Pattern a] where
    pretty [] = ""
    pretty ps = unwords (map pretty ps) <> " "

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty v => Pretty (Value v a) where
    pretty (Abs _ x t e) = "\\(" <> pretty x <> " : " <> pretty t
                                 <> ") -> " <> pretty e
    pretty (Promote _ e) = "[" <> pretty e <> "]"
    pretty (Pure _ e)    = "<" <> pretty e <> ">"
    pretty (Var _ x)     = pretty x
    pretty (NumInt n)    = show n
    pretty (NumFloat n)  = show n
    pretty (CharLiteral c) = show c
    pretty (StringLiteral s) = show s
    pretty (Constr _ s vs) | internalName s == "," =
      "(" <> intercalate ", " (map pretty vs) <> ")"
    pretty (Constr _ n []) = pretty n
    pretty (Constr _ n vs) = intercalate " " $ pretty n : map prettyNested vs
    pretty (Ext _ v) = pretty v

instance Pretty Id where
  pretty
    = if debugging
        then internalName
        else (stripMarker '`') . (stripMarker '.') . sourceName
    where
      stripMarker c [] = []
      stripMarker c (c':cs) | c == c' = cs
                            | otherwise = c' : stripMarker c cs


instance Pretty (Value v a) => Pretty (Expr v a) where
  pretty (App _ _ (App _ _ (Val _ _ (Constr _ x _)) t1) t2) | sourceName x == "," =
    "(" <> pretty t1 <> ", " <> pretty t2 <> ")"

  pretty (App _ _ e1 e2) =
    pretty e1 <> " " <> prettyNested e2

  pretty (Binop _ _ op e1 e2) =
    pretty e1 <> " " <> pretty op <> " " <> pretty e2

  pretty (LetDiamond _ _ v t e1 e2) =
    "let " <> pretty v <> " :" <> pretty t <> " <- "
          <> pretty e1 <> " in " <> pretty e2

  pretty (TryCatch _ _ _ e1 v t e2 e3) =
    "try " <> pretty e1 <> " as [" <> pretty v <> "] " <> (if t /= Nothing then ":" <> pretty t else "")   <> " in " 
          <> pretty e2 <> " catch " <> pretty e3
    
  pretty (Val _ _ _ v) = pretty v
  pretty (Case _ _ _ e ps) = "\n    (case " <> pretty e <> " of\n      "
                      <> intercalate ";\n      " (map (\(p, e') -> pretty p
                      <> " -> " <> pretty e') ps) <> ")"
  pretty (Hole _ _) = "?"

instance Pretty Operator where
  pretty = \case
    OpLesser          -> "<"
    OpLesserEq        -> "≤"
    OpGreater         -> ">"
    OpGreaterEq       -> "≥"
    OpEq              -> "≡"
    OpNotEq           -> "≠"
    OpPlus            -> "+"
    OpTimes           -> "*"
    OpMinus           -> "-"

ticks :: String -> String
ticks x = "`" <> x <> "`"

instance Pretty Int where
  pretty = show

instance Pretty Span where
  pretty
    | testing = const "(location redacted)"
    | otherwise = \case
      Span (0,0) _ "" -> "(unknown location)"
      Span (0,0) _ f  -> f
      Span pos   _ f  -> f <> ":" <> pretty pos

instance Pretty Pos where
    pretty (l, c) = show l <> ":" <> show c
