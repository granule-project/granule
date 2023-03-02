-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Granule.Syntax.Pretty where

import Data.Foldable (toList)
import Data.List (intercalate)
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers
import Language.Granule.Utils
import Language.Granule.Syntax.Program

-- Version of pretty that assumes the default Globals so as not to
-- propagate globals information around
prettyTrace :: Pretty t => t -> String
prettyTrace = let ?globals = mempty in pretty

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
    pretty (TyCon s) | internalName s == "Infinity" = "∞"
    pretty (TyCon s)      = pretty s
    pretty (TyVar v)      = pretty v
    pretty (TyInt n)      = show n
    pretty (TyGrade Nothing n)  = show n
    pretty (TyGrade (Just t) n)  = "(" <> show n <> " : " <> pretty t <> ")"
    pretty (TyRational n) = show n

    -- Non atoms
    pretty (Type 0) = "Type"

    pretty (Type l) =
      "Type " <> pretty l

    pretty (FunTy Nothing t1 t2)  =
      case t1 of
        FunTy{} -> "(" <> pretty t1 <> ") -> " <> pretty t2
        _ -> pretty t1 <> " -> " <> pretty t2

    pretty (FunTy (Just id) t1 t2)  =
      let pt1 = case t1 of FunTy{} -> "(" <> pretty t1 <> ")"; _ -> pretty t1
      in  "(" <> pretty id <> " : " <> pt1 <> ") -> " <> pretty t2

    pretty (Box c t) =
      case c of
        (TyCon (Id "Many" "Many")) -> "!" <> prettyNested t
        otherwise -> prettyNested t <> " [" <> pretty c <> "]"

    pretty (Diamond e t) =
      prettyNested t <> " <" <> pretty e <> ">"

    pretty (Star g t) =
      case g of
        (TyCon (Id "Unique" "Unique")) -> "*" <> prettyNested t
        otherwise -> prettyNested t <> " *" <> pretty g

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "," =
      "(" <> pretty t1 <> ", " <> pretty t2 <> ")"

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "×" =
      "(" <> pretty t1 <> " × " <> pretty t2 <> ")"

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == ",," =
      "(" <> pretty t1 <> " × " <> pretty t2 <> ")"

    pretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "&" =
      pretty t1 <> " & " <> pretty t2

    pretty (TyApp t1 t2)  =
      pretty t1 <> " " <> prettyNested t2

    pretty (TyInfix TyOpInterval t1 t2) =
      prettyNested t1 <> pretty TyOpInterval <> prettyNested t2

    pretty (TyInfix op t1 t2) =
      prettyNested t1 <> " " <> pretty op <> " " <> prettyNested t2

    pretty (TySet polarity ts) =
        "{" <> intercalate ", " (map pretty ts) <> "}"
      <> (if polarity == Opposite then "." else "")

    pretty (TySig t k) =
      "(" ++ pretty t ++ " : " ++ pretty k ++ ")"

    pretty (TyCase t ps) =
     "(case " <> pretty t <> " of "
                    <> intercalate "; " (map (\(p, t') -> pretty p
                    <> " : " <> pretty t') ps) <> ")"


instance Pretty TypeOperator where
  pretty = \case
   TyOpLesserNat       -> "<"
   TyOpLesserEq        -> "≤"
   TyOpLesserEqNat     -> ".≤"
   TyOpGreaterNat      -> ">"
   TyOpGreaterEq       -> "≥"
   TyOpGreaterEqNat    -> ".≥"
   TyOpEq              -> "≡"
   TyOpNotEq           -> "≠"
   TyOpPlus            -> "+"
   TyOpTimes           -> "*"
   TyOpMinus           -> "-"
   TyOpExpon           -> "^"
   TyOpMeet            -> "∧"
   TyOpJoin            -> "∨"
   TyOpInterval        -> ".."
   TyOpConverge        -> "#"

instance Pretty Module where
  pretty Mod
    { moduleAST = AST { dataTypes, definitions }
    , moduleName
    , moduleExtensions
    , moduleImports
    , moduleHiddenNames } =
    -- Module header (if it exists)
    (case moduleName of
        "" -> ""
        _ -> "module "
            <> moduleName
            <> " hiding ("
            <> (intercalate "," (map pretty (toList moduleHiddenNames)))
            <> ") where\n\n"
    )
    <> (unlines . map ("import " <>) . toList) moduleImports
    <> "\n\n" <> pretty' dataTypes
    <> "\n\n" <> pretty' definitions
    where
      pretty' :: Pretty l => [l] -> String
      pretty' = intercalate "\n\n" . map pretty

instance Pretty v => Pretty (Def v a) where
    pretty (Def _ v _ eqs (Forall _ [] [] t))
      = pretty v <> " : " <> pretty t <> "\n" <> pretty eqs
    pretty (Def _ v _ eqs tySch)
      = pretty v <> " : " <> pretty tySch <> "\n" <> pretty eqs

instance Pretty v => Pretty (EquationList v a) where
  pretty (EquationList _ v _ eqs) = intercalate ";\n" $ map pretty eqs

instance Pretty v => Pretty (Equation v a) where
  pretty (Equation _ v _ _ ps e) =
     pretty v <> (if length ps == 0 then "" else " ") <> unwords (map prettyNested ps) <> " = " <> pretty e

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
    pretty (PVar _ _ _ v)     = pretty v
    pretty (PWild _ _ _)      = "_"
    pretty (PBox _ _ _ p)     = "[" <> prettyNested p <> "]"
    pretty (PInt _ _ _ n)     = show n
    pretty (PFloat _ _ _ n)   = show n
    pretty (PConstr _ _ _ name args) | internalName name == "," = "(" <> intercalate ", " (map prettyNested args) <> ")"
    pretty (PConstr _ _ _ name args) = unwords (pretty name : map prettyNested args)

instance {-# OVERLAPS #-} Pretty [Pattern a] where
    pretty [] = ""
    pretty ps = unwords (map pretty ps) <> " "

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty v => Pretty (Value v a) where
    pretty (Abs _ x Nothing e) = "\\" <> pretty x <> " -> " <> pretty e
    pretty (Abs _ x t e) = "\\(" <> pretty x <> " : " <> pretty t
                                 <> ") -> " <> pretty e
    pretty (Promote _ e) = "[" <> pretty e <> "]"
    pretty (Pure _ e)    = "<" <> pretty e <> ">"
    pretty (Nec _ e)     = "*" <> pretty e
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
  pretty (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ x _)) t1) t2) | sourceName x == "," =
    "(" <> pretty t1 <> ", " <> pretty t2 <> ")"

  pretty (App _ _ _ (Val _ _ _ (Abs _ x _ e1)) e2) =
    "let " <> pretty x <> " = " <> pretty e2 <> " in " <> pretty e1

  pretty (App _ _ _ e1 e2) =
    prettyNested e1 <> " " <> prettyNested e2

  pretty (AppTy _ _ _ e1 t) =
    prettyNested e1 <> " @ " <> prettyNested t

  pretty (Binop _ _ _ op e1 e2) =
    pretty e1 <> " " <> pretty op <> " " <> pretty e2

  pretty (LetDiamond _ _ _ v t e1 e2) =
    "let " <> pretty v <> " :" <> pretty t <> " <- "
          <> pretty e1 <> " in " <> pretty e2

  pretty (TryCatch _ _ _ e1 v t e2 e3) =
    "try " <> pretty e1 <> " as [" <> pretty v <> "] " <> (if t /= Nothing then ":" <> pretty t else "")   <> " in "
          <> pretty e2 <> " catch " <> pretty e3

  pretty (Val _ _ _ v) = pretty v
  pretty (Case _ _ _ e ps) = "\n    (case " <> pretty e <> " of\n      "
                      <> intercalate ";\n      " (map (\(p, e') -> pretty p
                      <> " -> " <> pretty e') ps) <> ")"
  pretty (Hole _ _ _ []) = "?"
  pretty (Hole _ _ _ vs) = "{!" <> unwords (map pretty vs) <> "!}"

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
    OpDiv             -> "/"
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
