-- Pretty printer for Granule
--  It is not especially pretty.
-- Useful in debugging and error messages

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}

module Language.Granule.Syntax.Pretty (Pretty(..), prettyTrace, prettyNested, ticks, prettyDebug, prettyDoc) where

import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Ratio (numerator, denominator)
import qualified Data.Text as T
import qualified Prettyprinter as P
import Prettyprinter ((<+>))
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils

-- Version of pretty that assumes the default Globals so as not to
-- propagate globals information around
prettyTrace :: Pretty t => t -> String
prettyTrace = let ?globals = mempty in pretty

prettyDebug :: (?globals :: Globals) => Pretty t => t -> String
prettyDebug x =
  let ?globals = ?globals { globalsDebugging = Just True }
  in pretty x

prettyDoc :: (?globals :: Globals) => Pretty t => t -> String
prettyDoc x =
  let ?globals = ?globals { globalsDocMode = Just True }
  in pretty x

prettyNested :: (?globals :: Globals, Term a, Pretty a) => a -> String
prettyNested e =
  if isLexicallyAtomic e then pretty e else "(" <> pretty e <> ")"


-- The pretty printer class
class Pretty t where
    -- `pretty` pretty printers something at nesting level `l`
    pretty :: (?globals :: Globals) => t -> String

-- Prettyprinter based functions

data Annotation = Keyword | ConstName | Coeff | Eff | Uniq | Perm

instance Show Annotation where
  show Keyword = "keyword"
  show ConstName = "constName"
  show Coeff = "coeff"
  show Eff = "eff"
  show Uniq = "uniq"
  show Perm = "perm"


class PrettyNew a where
  pretty_new :: (?globals :: Globals) => a -> P.Doc Annotation

instance PrettyNew Int where
  pretty_new n = P.pretty (show n)

prettyNestedNew :: (?globals :: Globals, Term a, PrettyNew a) => a -> P.Doc Annotation
prettyNestedNew e =
  if isLexicallyAtomic e then pretty_new e else P.parens $ pretty_new e

annKeyword :: P.Doc Annotation -> P.Doc Annotation
annKeyword = P.annotate Keyword

annConstName :: P.Doc Annotation -> P.Doc Annotation
annConstName = P.annotate ConstName

annCoeff :: P.Doc Annotation -> P.Doc Annotation
annCoeff = P.annotate Coeff

annEff :: P.Doc Annotation -> P.Doc Annotation
annEff = P.annotate Eff

annUniq :: P.Doc Annotation -> P.Doc Annotation
annUniq = P.annotate Uniq

annPerm :: P.Doc Annotation -> P.Doc Annotation
annPerm = P.annotate Perm

renderHtml :: P.SimpleDocStream Annotation -> String
renderHtml P.SFail = error "uncaught fail"
renderHtml P.SEmpty = ""
renderHtml (P.SChar c x) = c : renderHtml x
renderHtml (P.SText _ t x) = T.unpack t <> renderHtml x
renderHtml (P.SLine i x) = "\n" <> replicate i ' ' <> renderHtml x
renderHtml (P.SAnnPush a x) = "<span class='" <> show a <> "'>" <> renderHtml x
renderHtml (P.SAnnPop x) = "</span>" <> renderHtml x

-- Mostly for debugging

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b) => Pretty (a, b) where
   pretty (a, b) = "(" <> pretty a <> ", " <> pretty b <> ")"

instance {-# OVERLAPPABLE #-} (PrettyNew a, PrettyNew b) => PrettyNew (a, b) where
   pretty_new (a, b) = "(" <> pretty_new a <> ", " <> pretty_new b <> ")"

instance {-# OVERLAPS #-} Pretty (Id, Type) where
   pretty (a, b) = "(" <> pretty a <> " : " <> pretty b <> ")"

instance {-# OVERLAPS #-} PrettyNew (Id, Type) where
   pretty_new (a, b) = "(" <> pretty_new a <> " : " <> pretty_new b <> ")"

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b, Pretty c) => Pretty (a, b,c) where
   pretty (a, b, c) = "(" <> pretty a <> ", " <> pretty b <> "," <> pretty c <> ")"

instance {-# OVERLAPS #-} Pretty String where
   pretty s = s

instance Pretty () where
   pretty () = ""

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
   pretty xs = "[" <> intercalate "," (map pretty xs) <> "]"

-- Pretty printing for type variable contexts
instance Pretty q => Pretty [(Id, (Type, q))] where
  pretty = (intercalate ", ") . (map prettyAssignment)
    where
      prettyAssignment (v, (ty, qu)) = pretty qu <> pretty v <> " : " <> pretty ty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left a) = pretty a
  pretty (Right b) = pretty b

-- Core pretty printers

instance Pretty TypeScheme where
    pretty (Forall _ vs cs t) = kVars vs <> constraints cs <> pretty t
      where
        kVars [] = ""
        kVars vs = docSpan "keyword" "forall" <> " {" <> intercalate ", " (map prettyKindSignatures vs) <> "} . "
        prettyKindSignatures (var, kind) = pretty var <> " : " <> pretty kind
        constraints [] = ""
        constraints cs = "{" <> intercalate ", " (map pretty cs) <> "} =>\n    "

instance PrettyNew TypeScheme where
    pretty_new (Forall _ vs cs t) = kVars vs <> constraints cs <> pretty_new t
      where
        kVars [] = ""
        kVars vs = annKeyword "forall" <+> P.braces (P.cat (P.punctuate ", " (map prettyKindSignatures vs))) <> " . "
        prettyKindSignatures (var, kind) = pretty_new var <+> ":" <+> pretty_new kind
        constraints [] = ""
        constraints cs = P.braces (P.cat (P.punctuate ", " (map pretty_new cs))) <+> "=>\n    "

instance Pretty Type where
    -- Atoms
    pretty (TyCon s) | internalName s == "Infinity" = docSpan "constName" "∞"
    pretty (TyCon s)      = docSpan "constName" (pretty s)
    pretty (TyVar v)      = pretty v
    pretty (TyInt n)      = show n
    pretty (TyGrade Nothing n)  = show n
    pretty (TyGrade (Just t) n)  = "(" <> show n <> " : " <> pretty t <> ")"
    pretty (TyRational n) = show n
    pretty (TyFraction f) = let (n, d) = (numerator f, denominator f) in
      if d == 1 then
        show n
      else
        show n <> "/" <> show d

    -- Non atoms
    pretty (Type 0) = docSpan "constName" "Type"

    pretty (Type l) =
      docSpan "constName" ("Type " <> pretty l)

    pretty (FunTy Nothing Nothing t1 t2)  =
      prettyNested t1 <> " -> " <> pretty t2

    pretty (FunTy Nothing (Just coeffect) t1 t2)  =
      prettyNested t1 <> " % " <> docSpan "coeff" (pretty coeffect) <>  " -> " <> pretty t2

    pretty (FunTy (Just id) Nothing t1 t2)  =
      let pt1 = case t1 of FunTy{} -> "(" <> pretty t1 <> ")"; _ -> pretty t1
      in  "(" <> pretty id <> " : " <> pt1 <> ") -> " <> pretty t2

    pretty (FunTy (Just id) (Just coeffect) t1 t2)  =
      let pt1 = case t1 of FunTy{} -> "(" <> pretty t1 <> ")"; _ -> pretty t1
      in  "(" <> pretty id <> " : " <> pt1 <> ") % " <> docSpan "coeff" (pretty coeffect) <> " -> " <> pretty t2

    pretty (Box c t) =
      case c of
        (TyCon (Id "Many" "Many")) -> docSpan "coeff" ("!" <> prettyNested t)
        otherwise -> prettyNested t <> " [" <> docSpan "coeff" (pretty c) <> "]"

    pretty (Diamond e t) =
      prettyNested t <> " <" <> docSpan "eff" (pretty e) <> ">"

    pretty (Star g t) =
      case g of
        (TyCon (Id "Unique" "Unique")) -> docSpan "uniq" ("*" <> prettyNested t)
        otherwise -> prettyNested t <> " *" <> docSpan "uniq" (pretty g)

    pretty (Borrow p t) =
      case p of
        (TyCon (Id "Star" "Star")) -> docSpan "uniq" ("*" <> prettyNested t)
        otherwise -> docSpan "perm" ("& " <> prettyNested p <> " " <> prettyNested t)

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

    pretty (TyInfix TyOpMutable t1 _) =
      pretty TyOpMutable <> " " <> prettyNested t1

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

    pretty (TyExists var k t) =
      docSpan "keyword" "exists" <> " {" <> pretty var <> " : " <> pretty k <> "} . " <> pretty t

    pretty (TyForall var k t) =
      docSpan "keyword" "forall" <> " {" <> pretty var <> " : " <> pretty k <> "} . " <> pretty t
    
    pretty (TyName n) = "id" ++ show n

instance PrettyNew Type where
    -- Atoms
    pretty_new (TyCon s) | internalName s == "Infinity" = annConstName "∞"
    pretty_new (TyCon s)      = annConstName (pretty_new s)
    pretty_new (TyVar v)      = pretty_new v
    pretty_new (TyInt n)      = P.pretty (show n)
    pretty_new (TyGrade Nothing n)  = P.pretty (show n)
    pretty_new (TyGrade (Just t) n)  = P.parens $ P.pretty (show n) <+> ":" <+> pretty_new t 
    pretty_new (TyRational n) = P.pretty $ show n
    pretty_new (TyFraction f) = let (n, d) = (numerator f, denominator f) in
      if d == 1 then
        P.pretty (show n)
      else
        P.pretty (show n) <> "/" <> P.pretty (show d)

    -- Non atoms
    pretty_new (Type 0) = annConstName "Type"

    pretty_new (Type l) =
      annConstName ("Type " <> pretty_new l)

    pretty_new (FunTy Nothing Nothing t1 t2)  =
      prettyNestedNew t1 <+> "->" <+> pretty_new t2

    pretty_new (FunTy Nothing (Just coeffect) t1 t2)  =
      prettyNestedNew t1 <+> "%" <+> annCoeff (pretty_new coeffect) <+> "->" <+> pretty_new t2

    pretty_new (FunTy (Just id) Nothing t1 t2)  =
      let pt1 = case t1 of FunTy{} -> P.parens (pretty_new t1); _ -> pretty_new t1
      in  P.parens (pretty_new id <+> ":" <+> pt1) <+> "->" <+> pretty_new t2

    pretty_new (FunTy (Just id) (Just coeffect) t1 t2)  =
      let pt1 = case t1 of FunTy{} -> P.parens (pretty_new t1); _ -> pretty_new t1
      in  P.parens (pretty_new id <+> ":" <+> pt1) <+> "%" <+> annCoeff (pretty_new coeffect) <+> "->" <+> pretty_new t2

    pretty_new (Box c t) =
      case c of
        (TyCon (Id "Many" "Many")) -> annCoeff ("!" <> prettyNestedNew t)
        _ -> prettyNestedNew t <> P.brackets (annCoeff (pretty_new c))

    pretty_new (Diamond e t) =
      prettyNestedNew t <+> "<" <> annEff (pretty_new e) <> ">"

    pretty_new (Star g t) =
      case g of
        (TyCon (Id "Unique" "Unique")) -> annUniq ("*" <> prettyNestedNew t)
        _ -> prettyNestedNew t <+> "*" <> annUniq (pretty_new g)

    pretty_new (Borrow p t) =
      case p of
        (TyCon (Id "Star" "Star")) -> annUniq ("*" <> prettyNestedNew t)
        _ -> annPerm ("&" <+> prettyNestedNew p <+> prettyNestedNew t)

    pretty_new (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "," =
      P.parens $ pretty_new t1 <> "," <+> pretty_new t2

    pretty_new (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "×" =
      P.parens $ pretty_new t1 <+> "×" <+> pretty_new t2

    pretty_new (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == ",," =
      P.parens $ pretty_new t1 <+> "×" <+> pretty_new t2

    pretty_new (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "&" =
      pretty_new t1 <+> "&" <+> pretty_new t2

    pretty_new (TyApp t1 t2)  =
      pretty_new t1 <+> prettyNestedNew t2

    pretty_new (TyInfix TyOpInterval t1 t2) =
      prettyNestedNew t1 <> pretty_new TyOpInterval <> prettyNestedNew t2

    pretty_new (TyInfix TyOpMutable t1 _) =
      pretty_new TyOpMutable <+> prettyNestedNew t1

    pretty_new (TyInfix op t1 t2) =
      prettyNestedNew t1 <+> pretty_new op <+> prettyNestedNew t2

    pretty_new (TySet polarity ts) =
      P.braces (P.cat (P.punctuate ", " (map pretty_new ts)))
      <> (if polarity == Opposite then "." else "")

    pretty_new (TySig t k) =
      P.parens $ pretty_new t <+> ":" <+> pretty_new k

    pretty_new (TyCase t ps) =
     "(case" <+> pretty_new t <+> "of"
                    <+> P.cat (P.punctuate "; " (map (\(p, t') -> pretty_new p
                    <+> ":" <+> pretty_new t') ps)) <> ")"

    pretty_new (TyExists var k t) =
      annKeyword "exists" <+> P.braces (pretty_new var <+> ":" <+> pretty_new k) <+> "." <+> pretty_new t

    pretty_new (TyForall var k t) =
      annKeyword "forall" <+> P.braces (pretty_new var <+> ":" <+> pretty_new k) <+> "." <+> pretty_new t
    
    pretty_new (TyName n) = "id" <> P.pretty (show n)

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
   TyOpImpl            -> "=>"
   TyOpHsup            -> "⨱"
   TyOpMutable         -> "mut"

instance PrettyNew TypeOperator where
  pretty_new = \case
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
   TyOpImpl            -> "=>"
   TyOpHsup            -> "⨱"
   TyOpMutable         -> "mut"

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
    pretty (Def _ v _ (Just spec) eqs (Forall _ [] [] t))
      = pretty v <> " : " <> pretty t <> "\n" <> pretty spec <> "\n" <> pretty eqs
    pretty (Def _ v _ _ eqs (Forall _ [] [] t))
      = pretty v <> " : " <> pretty t <> "\n" <> pretty eqs
    pretty (Def _ v _ (Just spec) eqs tySch)
      = pretty v <> " : " <> pretty tySch <> "\n" <> pretty spec <> "\n" <> pretty eqs
    pretty (Def _ v _ _ eqs tySch)
      = pretty v <> " : " <> pretty tySch <> "\n" <> pretty eqs

instance Pretty v => Pretty (Spec v a) where
    pretty (Spec _ _ exs comps) = "spec" <> "\n" <> (intercalate "\n\t" $ map pretty exs) <> "\t" <> (intercalate "," $ map prettyComp comps)

instance Pretty v => Pretty (Example v a) where
    pretty (Example input output _) = pretty input <> " = " <> pretty output

instance Pretty v => Pretty (EquationList v a) where
  pretty (EquationList _ v _ eqs) = intercalate ";\n" $ map pretty eqs

instance Pretty v => Pretty (Equation v a) where
  pretty (Equation _ v _ _ ps e) =
     pretty v <> (if length ps == 0 then "" else " ") <> unwords (map prettyNested ps) <> " = " <> pretty e

instance Pretty DataDecl where
    pretty (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> (unwords . map pretty) tyVars <> " "
          ki = case kind of Nothing -> ""; Just k -> ": " <> pretty k <> " "
      in (docSpan "keyword" "data") <> " " <> (docSpan "constName" (pretty tyCon)) <> " " <> tvs <> ki <> (docSpan "keyword" "where") <> "\n    " <> prettyAlign dataConstrs
      where
        prettyAlign dataConstrs = intercalate "\n  ; " (map (pretty' indent) dataConstrs)
          where indent = maximum (map (length . internalName . dataConstrId) dataConstrs)
        pretty' col (DataConstrIndexed _ name typeScheme) =
          pretty name <> (replicate (col - (length $ pretty name)) ' ') <> " : " <> pretty typeScheme
        pretty' _   (DataConstrNonIndexed _ name params) = pretty name <> " " <> (intercalate " " $ map prettyNested params)


instance PrettyNew DataDecl where
    pretty_new (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> P.sep (map pretty_new tyVars) <> " "
          ki = case kind of Nothing -> ""; Just k -> ": " <> pretty_new k <> " "
      in annKeyword "data" <+> annConstName (pretty_new tyCon) <+> tvs <> ki <> annKeyword "where" <> "\n    " <> prettyAlign dataConstrs
      where
        prettyAlign dataConstrs = P.cat (P.punctuate "\n  ; " (map (pretty' indent) dataConstrs))
          where indent = maximum (map (length . internalName . dataConstrId) dataConstrs)
        pretty' col (DataConstrIndexed _ name typeScheme) =
          pretty_new name <> P.cat (map P.pretty (replicate (col - (length $ pretty name)) ' ')) <+> ":" <+> pretty_new typeScheme
        pretty' _   (DataConstrNonIndexed _ name params) = pretty_new name <+> P.cat (P.punctuate " " $ map prettyNestedNew params)

instance Pretty [DataConstr] where
    pretty = intercalate ";\n    " . map pretty

instance PrettyNew [DataConstr] where
    pretty_new xs = P.cat $ P.punctuate ";\n    " (map pretty_new xs)


instance Pretty DataConstr where
    pretty (DataConstrIndexed _ name typeScheme) = pretty name <> " : " <> pretty typeScheme
    pretty (DataConstrNonIndexed _ name params) = pretty name <> " " <> intercalate " " (map pretty params)

instance PrettyNew DataConstr where
    pretty_new (DataConstrIndexed _ name typeScheme) = pretty_new name <+> ":" <+> pretty_new typeScheme
    pretty_new (DataConstrNonIndexed _ name params) = pretty_new name <> " " <> P.cat (P.punctuate " " (map pretty_new params))

instance Pretty (Pattern a) where
    pretty (PVar _ _ _ v)     = pretty v
    pretty (PWild _ _ _)      = "_"
    pretty (PBox _ _ _ p)     = "[" <> prettyNested p <> "]"
    pretty (PInt _ _ _ n)     = show n
    pretty (PFloat _ _ _ n)   = show n
    pretty (PConstr _ _ _ name _ args) | internalName name == "," = "(" <> intercalate ", " (map prettyNested args) <> ")"
    pretty (PConstr _ _ _ name tyVarBindsRequested args) =
      unwords (pretty name : (map tyvarbinds tyVarBindsRequested ++ map prettyNested args))
        where tyvarbinds x = "{" <> pretty x <> "}"

instance PrettyNew (Pattern a) where
    pretty_new (PVar _ _ _ v)     = pretty_new v
    pretty_new PWild {}           = "_"
    pretty_new (PBox _ _ _ p)     = P.brackets $ prettyNestedNew p
    pretty_new (PInt _ _ _ n)     = P.pretty (show n)
    pretty_new (PFloat _ _ _ n)   = P.pretty (show n)
    pretty_new (PConstr _ _ _ name _ args) | internalName name == "," = P.parens $ P.cat $ P.punctuate ", " (map prettyNestedNew args)
    pretty_new (PConstr _ _ _ name tyVarBindsRequested args) =
      P.sep (pretty_new name : (map tyvarbinds tyVarBindsRequested ++ map prettyNestedNew args))
        where tyvarbinds x = P.braces $ pretty_new x

instance {-# OVERLAPS #-} Pretty [Pattern a] where
    pretty [] = ""
    pretty ps = unwords (map pretty ps) <> " "

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance PrettyNew t => PrettyNew (Maybe t) where
    pretty_new Nothing = "unknown"
    pretty_new (Just x) = pretty_new x

instance Pretty v => Pretty (Value v a) where
    pretty (Abs _ x Nothing e) = "\\" <> pretty x <> " -> " <> pretty e
    pretty (Abs _ x t e) = "\\(" <> pretty x <> " : " <> pretty t
                                 <> ") -> " <> pretty e
    pretty (Promote _ e) = "[" <> pretty e <> "]"
    pretty (Pure _ e)    = "<" <> pretty e <> ">"
    pretty (Nec _ e)     = "*" <> pretty e
    pretty (Ref _ e)     = "&" <> pretty e
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
    pretty (Pack s a ty e1 var k ty') =
      "pack <" <> pretty ty <> ", " <> pretty e1 <> "> "
      <> "as exists {" <> pretty var <> " : " <> pretty k <> "} . " <> pretty ty'
    pretty (TyAbs _ (Left (v, k)) e) =
      "/\\(" <> pretty v <> " : " <> pretty k <> ") -> " <> pretty e
    pretty (TyAbs _ (Right ids) e) =
      "/\\{" <> intercalate ", " (map pretty ids) <> "}"

instance PrettyNew v => PrettyNew (Value v a) where
    pretty_new (Abs _ x Nothing e) = "\\" <> pretty_new x <+> "->" <+> pretty_new e
    pretty_new (Abs _ x t e) = "\\(" <> pretty_new x <+> ":" <+> pretty_new t
                                 <> ") -> " <> pretty_new e
    pretty_new (Promote _ e) = P.brackets $ pretty_new e
    pretty_new (Pure _ e)    = "<" <> pretty_new e <> ">"
    pretty_new (Nec _ e)     = "*" <> pretty_new e
    pretty_new (Ref _ e)     = "&" <> pretty_new e
    pretty_new (Var _ x)     = pretty_new x
    pretty_new (NumInt n)    = P.pretty (show n)
    pretty_new (NumFloat n)  = P.pretty (show n)
    pretty_new (CharLiteral c) = P.pretty (show c)
    pretty_new (StringLiteral s) = P.pretty (show s)
    pretty_new (Constr _ s vs) | internalName s == "," =
      P.parens $ P.cat $ P.punctuate ", " (map pretty_new vs)
    pretty_new (Constr _ n []) = pretty_new n
    pretty_new (Constr _ n vs) = P.sep $ pretty_new n : map prettyNestedNew vs
    pretty_new (Ext _ v) = pretty_new v
    pretty_new (Pack s a ty e1 var k ty') =
      "pack <" <> pretty_new ty <> "," <+> pretty_new e1 <> ">"
      <+> "as exists {" <> pretty_new var <+> ":" <+> pretty_new k <> "} . " <> pretty_new ty'
    pretty_new (TyAbs _ (Left (v, k)) e) =
      "/\\(" <> pretty_new v <> " : " <> pretty_new k <> ") -> " <> pretty_new e
    pretty_new (TyAbs _ (Right ids) e) =
      "/\\{" <> P.cat (P.punctuate ", " (map pretty_new ids)) <> "}"

instance Pretty Id where
  pretty
    = if debugging
        then internalName
        else filter (\x -> x /= '.' && x /= '`') . sourceName

instance PrettyNew Id where
  pretty_new id = if debugging
        then P.pretty (internalName id)
        else P.pretty ((filter (\x -> x /= '.' && x /= '`') . sourceName) id)

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
  pretty (Hole _ _ _ [] Nothing) = "?"
  pretty (Hole _ _ _ [] (Just hints)) = "{!" <> pretty hints <> " !}"
  pretty (Hole _ _ _ vs _) = "{!" <> unwords (map pretty vs) <> "!}"

  pretty (Unpack _ _ _ tyVar var e1 e2) =
    "unpack <" <> pretty tyVar <> ", " <> pretty var <> "> = " <> pretty e1 <> " in " <> pretty e2

instance PrettyNew (Value v a) => PrettyNew (Expr v a) where
  pretty_new (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ x _)) t1) t2) | sourceName x == "," =
    P.parens $ pretty_new t1 <> "," <+> pretty_new t2

  pretty_new (App _ _ _ (Val _ _ _ (Abs _ x _ e1)) e2) =
    "let" <+> pretty_new x <+> "=" <+> pretty_new e2 <+> "in" <+> pretty_new e1

  pretty_new (App _ _ _ e1 e2) =
    prettyNestedNew e1 <+> prettyNestedNew e2

  pretty_new (AppTy _ _ _ e1 t) =
    prettyNestedNew e1 <+> "@" <+> prettyNestedNew t

  pretty_new (Binop _ _ _ op e1 e2) =
    pretty_new e1 <+> pretty_new op <+> pretty_new e2

  pretty_new (LetDiamond _ _ _ v t e1 e2) =
    "let" <+> pretty_new v <+> ":" <> pretty_new t <+> "<-"
          <+> pretty_new e1 <+> "in" <+> pretty_new e2

  pretty_new (TryCatch _ _ _ e1 v t e2 e3) =
    "try" <+> pretty_new e1 <+> "as [" <> pretty_new v <> "]" <+> (if t /= Nothing then ":" <> pretty_new t else "") <+> "in"
          <+> pretty_new e2 <+> "catch" <+> pretty_new e3

  pretty_new (Val _ _ _ v) = pretty_new v
  pretty_new (Case _ _ _ e ps) = "\n    (case " <> pretty_new e <> " of\n      "
                      <> P.cat (P.punctuate ";\n      " (map (\(p, e') -> pretty_new p
                      <> " -> " <> pretty_new e') ps)) <> ")"
  pretty_new (Hole _ _ _ [] Nothing) = "?"
  pretty_new (Hole _ _ _ [] (Just hints)) = "{!" <> pretty_new hints <> " !}"
  pretty_new (Hole _ _ _ vs _) = "{!" <> P.sep (map pretty_new vs) <> "!}"

  pretty_new (Unpack _ _ _ tyVar var e1 e2) =
    "unpack <" <> pretty_new tyVar <> ", " <> pretty_new var <> "> = " <> pretty_new e1 <> " in " <> pretty_new e2

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

instance PrettyNew Operator where
  pretty_new = \case
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

prettyComp :: (?globals :: Globals) => (Id, Maybe Type) -> String
prettyComp (var, Just ty) = pretty var <> " % " <> pretty ty
prettyComp (var, Nothing) = pretty var

instance {-# OVERLAPPABLE #-} Show a => Pretty a where
  pretty = show

instance Pretty Span where
  pretty
    | testing = const "(location redacted)"
    | otherwise = \case
      Span (0,0) _ "" -> "(unknown location)"
      Span (0,0) _ f  -> f
      Span pos   _ f  -> f <> ":" <> pretty pos

instance PrettyNew Span where
  pretty_new
    | testing = const "(location redacted)"
    | otherwise = \case
      Span (0,0) _ "" -> "(unknown location)"
      Span (0,0) _ f  -> P.pretty f
      Span pos   _ f  -> P.pretty f <> ":" <> pretty_new pos

instance Pretty Pos where
    pretty (l, c) = show l <> ":" <> show c

instance PrettyNew Pos where
    pretty_new (l, c) = P.pretty (show l) <> ":" <> P.pretty (show c)

instance Pretty Hints where
    pretty (Hints hSub hPrun hNoTime hLin hTime hIndex) = ""
      --  \case

      -- HSubtractive      -> " -s"
      -- HPruning          -> " -p"
      -- HNoMaxIntro       -> " -i"
      -- HMaxIntro x       -> " -i " <> show x
      -- HNoMaxElim        -> " -e"
      -- HMaxElim x        -> " -e " <> show x
      -- HSynNoTimeout     -> " -t"
      -- HSynTimeout x     -> " -t " <> show x
      -- HSynIndex x       -> " -n " <> show x
      -- HUseAllDefs       -> " -d"
      -- HUseDefs ids      -> " -d " <> (unwords $ map pretty ids)
      -- HUseRec           -> " -r"
      -- HGradeOnRule      -> " -g"

instance PrettyNew Hints where
  pretty_new (Hints _ _ _ _ _ _)= ""

docSpan :: (?globals :: Globals) => String -> String -> String
docSpan s x = if docMode then (spanP s x) else x

-- `spanP "keyword" "forall"` = `<span class='keyword'>forall</span>`
spanP :: String -> String -> String
spanP name = tagWithAttributesP "span" ("class='" <> name <> "'")

tagWithAttributesP :: String -> String -> String -> String
tagWithAttributesP name attributes content =
  "<" <> name <> " " <> attributes <> ">" <> content <> "</" <> name <> ">"

