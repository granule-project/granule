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

module Language.Granule.Syntax.Pretty (Pretty(..), Annotation, pretty, prettyTrace, prettyNestedNew, prettyNested, ticks, prettyDebug, prettyDoc) where

import Data.Foldable (toList)
import Data.Ratio (numerator, denominator)
import qualified Data.Text as T
import qualified Prettyprinter as P
import Prettyprinter ((<+>))
import Prettyprinter.Render.String
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils


layoutOptions :: P.LayoutOptions
layoutOptions = P.LayoutOptions P.Unbounded

-- Version of pretty that assumes the default Globals so as not to
-- propagate globals information around
prettyTrace :: Pretty t => t -> String
prettyTrace x =
  let ?globals = mempty in
  let doc = pretty_new x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderString docstream
  

prettyDebug :: (?globals :: Globals) => Pretty t => t -> String
prettyDebug x =
  let ?globals = ?globals { globalsDebugging = Just True } in
  let doc = pretty_new x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderString docstream

prettyDoc :: (?globals :: Globals) => Pretty t => t -> String
prettyDoc x =
  let ?globals = ?globals { globalsDocMode = Just True } in
  let doc = pretty_new x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderHtml docstream

pretty :: (?globals :: Globals, Pretty t) => t -> String
pretty x =
  let doc = pretty_new x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderString docstream


-- Prettyprinter based functions

data Annotation = Keyword | ConstName | Coeff | Eff | Uniq | Perm

instance Show Annotation where
  show Keyword = "keyword"
  show ConstName = "constName"
  show Coeff = "coeff"
  show Eff = "eff"
  show Uniq = "uniq"
  show Perm = "perm"


class Pretty a where
  pretty_new :: (?globals :: Globals) => a -> P.Doc Annotation

instance Pretty (P.Doc Annotation) where
  pretty_new = id

instance Pretty Int where
  pretty_new n = P.pretty (show n)

prettyNested :: (?globals :: Globals, Term a, Pretty a) => a -> String
prettyNested = pretty . prettyNestedNew

prettyNestedNew :: (?globals :: Globals, Term a, Pretty a) => a -> P.Doc Annotation
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
   pretty_new (a, b) = "(" <> pretty_new a <> ", " <> pretty_new b <> ")"

instance {-# OVERLAPS #-} Pretty (Id, Type) where
   pretty_new (a, b) = P.parens $ pretty_new a <> " : " <> pretty_new b

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b, Pretty c) => Pretty (a, b,c) where
   pretty_new (a, b, c) = P.parens $ pretty_new a <> ", " <> pretty_new b <> "," <> pretty_new c

instance Pretty () where
  pretty_new () = ""

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
   pretty_new xs = P.brackets $ mconcat $ P.punctuate "," (map pretty_new xs)

-- Pretty printing for type variable contexts
instance Pretty q => Pretty [(Id, (Type, q))] where
  pretty_new = mconcat . P.punctuate ", " . map prettyAssignment
    where
      prettyAssignment (v, (ty, qu)) = pretty_new qu <> pretty_new v <> " : " <> pretty_new ty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty_new (Left a) = pretty_new a
  pretty_new (Right b) = pretty_new b

-- Core pretty printers

instance Pretty TypeScheme where
    pretty_new (Forall _ vs cs t) = kVars vs <> constraints cs <> pretty_new t
      where
        kVars [] = ""
        kVars vs = annKeyword "forall" <+> P.braces (mconcat (P.punctuate ", " (map prettyKindSignatures vs))) <> " . "
        prettyKindSignatures (var, kind) = pretty_new var <+> ":" <+> pretty_new kind
        constraints [] = ""
        constraints cs = P.braces (mconcat (P.punctuate ", " (map pretty_new cs))) <+> "=>\n    "

instance Pretty Type where
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
        _ -> prettyNestedNew t <+> P.brackets (annCoeff (pretty_new c))

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
      P.braces (mconcat (P.punctuate ", " (map pretty_new ts)))
      <> (if polarity == Opposite then "." else "")

    pretty_new (TySig t k) =
      P.parens $ pretty_new t <+> ":" <+> pretty_new k

    pretty_new (TyCase t ps) =
     "(case" <+> pretty_new t <+> "of"
                    <+> mconcat (P.punctuate "; " (map (\(p, t') -> pretty_new p
                    <+> ":" <+> pretty_new t') ps)) <> ")"

    pretty_new (TyExists var k t) =
      annKeyword "exists" <+> P.braces (pretty_new var <+> ":" <+> pretty_new k) <+> "." <+> pretty_new t

    pretty_new (TyForall var k t) =
      annKeyword "forall" <+> P.braces (pretty_new var <+> ":" <+> pretty_new k) <+> "." <+> pretty_new t
    
    pretty_new (TyName n) = "id" <> P.pretty (show n)

instance Pretty TypeOperator where
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
  pretty_new (AST dataDecls defs imprts hidden name) =
    -- Module header (if it exists)
    (case name of
        Nothing -> ""
        Just name -> "module "
                  <> pretty_new name
                  <> " hiding ("
                  <> mconcat (P.punctuate "," (map pretty_new (toList hidden)))
                  <> ") where\n\n")
    <> (mconcat . P.punctuate "\n" . map prettyImport . toList) imprts
    <> "\n\n" <> pretty' dataDecls
    <> "\n\n" <> pretty' defs
    where
      prettyImport :: Import -> P.Doc Annotation
      prettyImport x = "import" <+> P.pretty x
      pretty' :: Pretty l => [l] -> P.Doc Annotation
      pretty' = mconcat . P.punctuate "\n\n" . map pretty_new

instance Pretty v => Pretty (Def v a) where
    pretty_new (Def _ v _ (Just spec) eqs (Forall _ [] [] t))
      = pretty_new v <> " : " <> pretty_new t <> "\n" <> pretty_new spec <> "\n" <> pretty_new eqs
    pretty_new (Def _ v _ _ eqs (Forall _ [] [] t))
      = pretty_new v <> " : " <> pretty_new t <> "\n" <> pretty_new eqs
    pretty_new (Def _ v _ (Just spec) eqs tySch)
      = pretty_new v <> " : " <> pretty_new tySch <> "\n" <> pretty_new spec <> "\n" <> pretty_new eqs
    pretty_new (Def _ v _ _ eqs tySch)
      = pretty_new v <> " : " <> pretty_new tySch <> "\n" <> pretty_new eqs

instance Pretty v => Pretty (Spec v a) where
    pretty_new (Spec _ _ exs comps) = "spec" <> "\n" <> mconcat (P.punctuate "\n\t" $ map pretty_new exs) <> "\t" <> mconcat (P.punctuate "," $ map prettyCompNew comps)

instance Pretty v => Pretty (Example v a) where
    pretty_new (Example input output _) = pretty_new input <> " = " <> pretty_new output

instance Pretty v => Pretty (EquationList v a) where
  pretty_new (EquationList _ v _ eqs) = mconcat $ P.punctuate ";\n" $ map pretty_new eqs


instance Pretty v => Pretty (Equation v a) where
  pretty_new (Equation _ v _ _ ps e) =
     pretty_new v <> (if null ps then "" else " ") <> P.sep (map prettyNestedNew ps) <> " = " <> pretty_new e

instance Pretty DataDecl where
    pretty_new (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> P.sep (map pretty_new tyVars) <> " "
          ki = case kind of Nothing -> ""; Just k -> ": " <> pretty_new k <> " "
      in annKeyword "data" <+> annConstName (pretty_new tyCon) <+> tvs <> ki <> annKeyword "where" <> "\n    " <> prettyAlign dataConstrs
      where
        prettyAlign dataConstrs = mconcat (P.punctuate "\n  ; " (map (pretty' indent) dataConstrs))
          where indent = maximum (map (length . internalName . dataConstrId) dataConstrs)
        pretty' col (DataConstrIndexed _ name typeScheme) =
          pretty_new name <> mconcat (map P.pretty (replicate (col - (length $ pretty name)) ' ')) <+> ":" <+> pretty_new typeScheme
        pretty' _   (DataConstrNonIndexed _ name params) = pretty_new name <+> mconcat (P.punctuate " " $ map prettyNestedNew params)

instance Pretty [DataConstr] where
    pretty_new xs = mconcat $ P.punctuate ";\n    " (map pretty_new xs)

instance Pretty DataConstr where
    pretty_new (DataConstrIndexed _ name typeScheme) = pretty_new name <+> ":" <+> pretty_new typeScheme
    pretty_new (DataConstrNonIndexed _ name params) = pretty_new name <> " " <> mconcat (P.punctuate " " (map pretty_new params))

instance Pretty (Pattern a) where
    pretty_new (PVar _ _ _ v)     = pretty_new v
    pretty_new PWild {}           = "_"
    pretty_new (PBox _ _ _ p)     = P.brackets $ prettyNestedNew p
    pretty_new (PInt _ _ _ n)     = P.pretty (show n)
    pretty_new (PFloat _ _ _ n)   = P.pretty (show n)
    pretty_new (PConstr _ _ _ name _ args) | internalName name == "," = P.parens $ mconcat $ P.punctuate ", " (map prettyNestedNew args)
    pretty_new (PConstr _ _ _ name tyVarBindsRequested args) =
      P.sep (pretty_new name : (map tyvarbinds tyVarBindsRequested ++ map prettyNestedNew args))
        where tyvarbinds x = P.braces $ pretty_new x

instance Pretty t => Pretty (Maybe t) where
    pretty_new Nothing = "unknown"
    pretty_new (Just x) = pretty_new x

instance Pretty v => Pretty (Value v a) where
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
      P.parens $ mconcat $ P.punctuate ", " (map pretty_new vs)
    pretty_new (Constr _ n []) = pretty_new n
    pretty_new (Constr _ n vs) = P.sep $ pretty_new n : map prettyNestedNew vs
    pretty_new (Ext _ v) = pretty_new v
    pretty_new (Pack s a ty e1 var k ty') =
      "pack <" <> pretty_new ty <> "," <+> pretty_new e1 <> ">"
      <+> "as exists {" <> pretty_new var <+> ":" <+> pretty_new k <> "} . " <> pretty_new ty'
    pretty_new (TyAbs _ (Left (v, k)) e) =
      "/\\(" <> pretty_new v <> " : " <> pretty_new k <> ") -> " <> pretty_new e
    pretty_new (TyAbs _ (Right ids) e) =
      "/\\{" <> mconcat (P.punctuate ", " (map pretty_new ids)) <> "}"


instance Pretty Id where
  pretty_new id = if debugging
        then P.pretty (internalName id)
        else P.pretty ((filter (\x -> x /= '.' && x /= '`') . sourceName) id)

instance Pretty (Value v a) => Pretty (Expr v a) where
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
                      <> mconcat (P.punctuate ";\n      " (map (\(p, e') -> pretty_new p
                      <> " -> " <> pretty_new e') ps)) <> ")"
  pretty_new (Hole _ _ _ [] Nothing) = "?"
  pretty_new (Hole _ _ _ [] (Just hints)) = "{!" <> pretty_new hints <> " !}"
  pretty_new (Hole _ _ _ vs _) = "{!" <> P.sep (map pretty_new vs) <> "!}"

  pretty_new (Unpack _ _ _ tyVar var e1 e2) =
    "unpack <" <> pretty_new tyVar <> ", " <> pretty_new var <> "> = " <> pretty_new e1 <> " in " <> pretty_new e2

instance Pretty Operator where
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

prettyCompNew :: (?globals :: Globals) => (Id, Maybe Type) -> P.Doc Annotation
prettyCompNew (var, Just ty) = pretty_new var <> " % " <> pretty_new ty
prettyCompNew (var, Nothing) = pretty_new var

instance Pretty Span where
  pretty_new
    | testing = const "(location redacted)"
    | otherwise = \case
      Span (0,0) _ "" -> "(unknown location)"
      Span (0,0) _ f  -> P.pretty f
      Span pos   _ f  -> P.pretty f <> ":" <> pretty_new pos

instance Pretty Pos where
    pretty_new (l, c) = P.pretty (show l) <> ":" <> P.pretty (show c)

instance Pretty Hints where
  pretty_new (Hints _ _ _ _ _ _)= ""
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
