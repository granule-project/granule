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
  let doc = wlpretty x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderString docstream
  

prettyDebug :: (?globals :: Globals) => Pretty t => t -> String
prettyDebug x =
  let ?globals = ?globals { globalsDebugging = Just True } in
  let doc = wlpretty x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderString docstream

prettyDoc :: (?globals :: Globals) => Pretty t => t -> String
prettyDoc x =
  let ?globals = ?globals { globalsDocMode = Just True } in
  let doc = wlpretty x in
  let docstream = P.layoutPretty layoutOptions doc in
  renderHtml docstream

pretty :: (?globals :: Globals, Pretty t) => t -> String
pretty x =
  let doc = wlpretty x in
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
  wlpretty :: (?globals :: Globals) => a -> P.Doc Annotation

instance Pretty (P.Doc Annotation) where
  wlpretty = id

instance Pretty Int where
  wlpretty n = P.pretty (show n)

prettyNested :: (?globals :: Globals, Term a, Pretty a) => a -> String
prettyNested = pretty . prettyNestedNew

prettyNestedNew :: (?globals :: Globals, Term a, Pretty a) => a -> P.Doc Annotation
prettyNestedNew e =
  if isLexicallyAtomic e then wlpretty e else P.parens $ wlpretty e

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
   wlpretty (a, b) = "(" <> wlpretty a <> ", " <> wlpretty b <> ")"

instance {-# OVERLAPS #-} Pretty (Id, Type) where
   wlpretty (a, b) = P.parens $ wlpretty a <> " : " <> wlpretty b

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b, Pretty c) => Pretty (a, b,c) where
   wlpretty (a, b, c) = P.parens $ wlpretty a <> ", " <> wlpretty b <> "," <> wlpretty c

instance Pretty () where
  wlpretty () = ""

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
   wlpretty xs = P.brackets $ mconcat $ P.punctuate "," (map wlpretty xs)

-- Pretty printing for type variable contexts
instance Pretty q => Pretty [(Id, (Type, q))] where
  wlpretty = mconcat . P.punctuate ", " . map prettyAssignment
    where
      prettyAssignment (v, (ty, qu)) = wlpretty qu <> wlpretty v <> " : " <> wlpretty ty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  wlpretty (Left a) = wlpretty a
  wlpretty (Right b) = wlpretty b

-- Core pretty printers

instance Pretty TypeScheme where
    wlpretty (Forall _ vs cs t) = kVars vs <> constraints cs <> wlpretty t
      where
        kVars [] = ""
        kVars vs = annKeyword "forall" <+> P.braces (mconcat (P.punctuate ", " (map prettyKindSignatures vs))) <> " . "
        prettyKindSignatures (var, kind) = wlpretty var <+> ":" <+> wlpretty kind
        constraints [] = ""
        constraints cs = P.braces (mconcat (P.punctuate ", " (map wlpretty cs))) <+> "=>\n    "

instance Pretty Type where
    -- Atoms
    wlpretty (TyCon s) | internalName s == "Infinity" = annConstName "∞"
    wlpretty (TyCon s)      = annConstName (wlpretty s)
    wlpretty (TyVar v)      = wlpretty v
    wlpretty (TyInt n)      = P.pretty (show n)
    wlpretty (TyGrade Nothing n)  = P.pretty (show n)
    wlpretty (TyGrade (Just t) n)  = P.parens $ P.pretty (show n) <+> ":" <+> wlpretty t 
    wlpretty (TyRational n) = P.pretty $ show n
    wlpretty (TyFraction f) = let (n, d) = (numerator f, denominator f) in
      if d == 1 then
        P.pretty (show n)
      else
        P.pretty (show n) <> "/" <> P.pretty (show d)

    -- Non atoms
    wlpretty (Type 0) = annConstName "Type"

    wlpretty (Type l) =
      annConstName ("Type " <> wlpretty l)

    wlpretty (FunTy Nothing Nothing t1 t2)  =
      prettyNestedNew t1 <+> "->" <+> wlpretty t2

    wlpretty (FunTy Nothing (Just coeffect) t1 t2)  =
      prettyNestedNew t1 <+> "%" <+> annCoeff (wlpretty coeffect) <+> "->" <+> wlpretty t2

    wlpretty (FunTy (Just id) Nothing t1 t2)  =
      let pt1 = case t1 of FunTy{} -> P.parens (wlpretty t1); _ -> wlpretty t1
      in  P.parens (wlpretty id <+> ":" <+> pt1) <+> "->" <+> wlpretty t2

    wlpretty (FunTy (Just id) (Just coeffect) t1 t2)  =
      let pt1 = case t1 of FunTy{} -> P.parens (wlpretty t1); _ -> wlpretty t1
      in  P.parens (wlpretty id <+> ":" <+> pt1) <+> "%" <+> annCoeff (wlpretty coeffect) <+> "->" <+> wlpretty t2

    wlpretty (Box c t) =
      case c of
        (TyCon (Id "Many" "Many")) -> annCoeff ("!" <> prettyNestedNew t)
        _ -> prettyNestedNew t <+> P.brackets (annCoeff (wlpretty c))

    wlpretty (Diamond e t) =
      prettyNestedNew t <+> "<" <> annEff (wlpretty e) <> ">"

    wlpretty (Star g t) =
      case g of
        (TyCon (Id "Unique" "Unique")) -> annUniq ("*" <> prettyNestedNew t)
        _ -> prettyNestedNew t <+> "*" <> annUniq (wlpretty g)

    wlpretty (Borrow p t) =
      case p of
        (TyCon (Id "Star" "Star")) -> annUniq ("*" <> prettyNestedNew t)
        _ -> annPerm ("&" <+> prettyNestedNew p <+> prettyNestedNew t)

    wlpretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "," =
      P.parens $ wlpretty t1 <> "," <+> wlpretty t2

    wlpretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "×" =
      P.parens $ wlpretty t1 <+> "×" <+> wlpretty t2

    wlpretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == ",," =
      P.parens $ wlpretty t1 <+> "×" <+> wlpretty t2

    wlpretty (TyApp (TyApp (TyCon x) t1) t2) | sourceName x == "&" =
      wlpretty t1 <+> "&" <+> wlpretty t2

    wlpretty (TyApp t1 t2)  =
      wlpretty t1 <+> prettyNestedNew t2

    wlpretty (TyInfix TyOpInterval t1 t2) =
      prettyNestedNew t1 <> wlpretty TyOpInterval <> prettyNestedNew t2

    wlpretty (TyInfix TyOpMutable t1 _) =
      wlpretty TyOpMutable <+> prettyNestedNew t1

    wlpretty (TyInfix op t1 t2) =
      prettyNestedNew t1 <+> wlpretty op <+> prettyNestedNew t2

    wlpretty (TySet polarity ts) =
      P.braces (mconcat (P.punctuate ", " (map wlpretty ts)))
      <> (if polarity == Opposite then "." else "")

    wlpretty (TySig t k) =
      P.parens $ wlpretty t <+> ":" <+> wlpretty k

    wlpretty (TyCase t ps) =
     "(case" <+> wlpretty t <+> "of"
                    <+> mconcat (P.punctuate "; " (map (\(p, t') -> wlpretty p
                    <+> ":" <+> wlpretty t') ps)) <> ")"

    wlpretty (TyExists var k t) =
      annKeyword "exists" <+> P.braces (wlpretty var <+> ":" <+> wlpretty k) <+> "." <+> wlpretty t

    wlpretty (TyForall var k t) =
      annKeyword "forall" <+> P.braces (wlpretty var <+> ":" <+> wlpretty k) <+> "." <+> wlpretty t
    
    wlpretty (TyName n) = "id" <> P.pretty (show n)

instance Pretty TypeOperator where
  wlpretty = \case
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
  wlpretty (AST dataDecls defs imprts hidden name) =
    -- Module header (if it exists)
    (case name of
        Nothing -> ""
        Just name -> "module "
                  <> wlpretty name
                  <> " hiding ("
                  <> mconcat (P.punctuate "," (map wlpretty (toList hidden)))
                  <> ") where\n\n")
    <> (mconcat . P.punctuate "\n" . map prettyImport . toList) imprts
    <> "\n\n" <> pretty' dataDecls
    <> "\n\n" <> pretty' defs
    where
      prettyImport :: Import -> P.Doc Annotation
      prettyImport x = "import" <+> P.pretty x
      pretty' :: Pretty l => [l] -> P.Doc Annotation
      pretty' = mconcat . P.punctuate "\n\n" . map wlpretty

instance Pretty v => Pretty (Def v a) where
    wlpretty (Def _ v _ (Just spec) eqs (Forall _ [] [] t))
      = wlpretty v <> " : " <> wlpretty t <> "\n" <> wlpretty spec <> "\n" <> wlpretty eqs
    wlpretty (Def _ v _ _ eqs (Forall _ [] [] t))
      = wlpretty v <> " : " <> wlpretty t <> "\n" <> wlpretty eqs
    wlpretty (Def _ v _ (Just spec) eqs tySch)
      = wlpretty v <> " : " <> wlpretty tySch <> "\n" <> wlpretty spec <> "\n" <> wlpretty eqs
    wlpretty (Def _ v _ _ eqs tySch)
      = wlpretty v <> " : " <> wlpretty tySch <> "\n" <> wlpretty eqs

instance Pretty v => Pretty (Spec v a) where
    wlpretty (Spec _ _ exs comps) = "spec" <> "\n" <> mconcat (P.punctuate "\n\t" $ map wlpretty exs) <> "\t" <> mconcat (P.punctuate "," $ map prettyCompNew comps)

instance Pretty v => Pretty (Example v a) where
    wlpretty (Example input output _) = wlpretty input <> " = " <> wlpretty output

instance Pretty v => Pretty (EquationList v a) where
  wlpretty (EquationList _ v _ eqs) = mconcat $ P.punctuate ";\n" $ map wlpretty eqs


instance Pretty v => Pretty (Equation v a) where
  wlpretty (Equation _ v _ _ ps e) =
     wlpretty v <> (if null ps then "" else " ") <> P.sep (map prettyNestedNew ps) <> " = " <> wlpretty e

instance Pretty DataDecl where
    wlpretty (DataDecl _ tyCon tyVars kind dataConstrs) =
      let tvs = case tyVars of [] -> ""; _ -> P.sep (map wlpretty tyVars) <> " "
          ki = case kind of Nothing -> ""; Just k -> ": " <> wlpretty k <> " "
      in annKeyword "data" <+> annConstName (wlpretty tyCon) <+> tvs <> ki <> annKeyword "where" <> "\n    " <> prettyAlign dataConstrs
      where
        prettyAlign dataConstrs = mconcat (P.punctuate "\n  ; " (map (pretty' indent) dataConstrs))
          where indent = maximum (map (length . internalName . dataConstrId) dataConstrs)
        pretty' col (DataConstrIndexed _ name typeScheme) =
          wlpretty name <> mconcat (map P.pretty (replicate (col - (length $ pretty name)) ' ')) <+> ":" <+> wlpretty typeScheme
        pretty' _   (DataConstrNonIndexed _ name params) = wlpretty name <+> mconcat (P.punctuate " " $ map prettyNestedNew params)

instance Pretty [DataConstr] where
    wlpretty xs = mconcat $ P.punctuate ";\n    " (map wlpretty xs)

instance Pretty DataConstr where
    wlpretty (DataConstrIndexed _ name typeScheme) = wlpretty name <+> ":" <+> wlpretty typeScheme
    wlpretty (DataConstrNonIndexed _ name params) = wlpretty name <> " " <> mconcat (P.punctuate " " (map wlpretty params))

instance Pretty (Pattern a) where
    wlpretty (PVar _ _ _ v)     = wlpretty v
    wlpretty PWild {}           = "_"
    wlpretty (PBox _ _ _ p)     = P.brackets $ prettyNestedNew p
    wlpretty (PInt _ _ _ n)     = P.pretty (show n)
    wlpretty (PFloat _ _ _ n)   = P.pretty (show n)
    wlpretty (PConstr _ _ _ name _ args) | internalName name == "," = P.parens $ mconcat $ P.punctuate ", " (map prettyNestedNew args)
    wlpretty (PConstr _ _ _ name tyVarBindsRequested args) =
      P.sep (wlpretty name : (map tyvarbinds tyVarBindsRequested ++ map prettyNestedNew args))
        where tyvarbinds x = P.braces $ wlpretty x

instance Pretty t => Pretty (Maybe t) where
    wlpretty Nothing = "unknown"
    wlpretty (Just x) = wlpretty x

instance Pretty v => Pretty (Value v a) where
    wlpretty (Abs _ x Nothing e) = "\\" <> wlpretty x <+> "->" <+> wlpretty e
    wlpretty (Abs _ x t e) = "\\(" <> wlpretty x <+> ":" <+> wlpretty t
                                 <> ") -> " <> wlpretty e
    wlpretty (Promote _ e) = P.brackets $ wlpretty e
    wlpretty (Pure _ e)    = "<" <> wlpretty e <> ">"
    wlpretty (Nec _ e)     = "*" <> wlpretty e
    wlpretty (Ref _ e)     = "&" <> wlpretty e
    wlpretty (Var _ x)     = wlpretty x
    wlpretty (NumInt n)    = P.pretty (show n)
    wlpretty (NumFloat n)  = P.pretty (show n)
    wlpretty (CharLiteral c) = P.pretty (show c)
    wlpretty (StringLiteral s) = P.pretty (show s)
    wlpretty (Constr _ s vs) | internalName s == "," =
      P.parens $ mconcat $ P.punctuate ", " (map wlpretty vs)
    wlpretty (Constr _ n []) = wlpretty n
    wlpretty (Constr _ n vs) = P.sep $ wlpretty n : map prettyNestedNew vs
    wlpretty (Ext _ v) = wlpretty v
    wlpretty (Pack s a ty e1 var k ty') =
      "pack <" <> wlpretty ty <> "," <+> wlpretty e1 <> ">"
      <+> "as exists {" <> wlpretty var <+> ":" <+> wlpretty k <> "} . " <> wlpretty ty'
    wlpretty (TyAbs _ (Left (v, k)) e) =
      "/\\(" <> wlpretty v <> " : " <> wlpretty k <> ") -> " <> wlpretty e
    wlpretty (TyAbs _ (Right ids) e) =
      "/\\{" <> mconcat (P.punctuate ", " (map wlpretty ids)) <> "}"


instance Pretty Id where
  wlpretty id = if debugging
        then P.pretty (internalName id)
        else P.pretty ((filter (\x -> x /= '.' && x /= '`') . sourceName) id)

instance Pretty (Value v a) => Pretty (Expr v a) where
  wlpretty (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ x _)) t1) t2) | sourceName x == "," =
    P.parens $ wlpretty t1 <> "," <+> wlpretty t2

  wlpretty (App _ _ _ (Val _ _ _ (Abs _ x _ e1)) e2) =
    "let" <+> wlpretty x <+> "=" <+> wlpretty e2 <+> "in" <+> wlpretty e1

  wlpretty (App _ _ _ e1 e2) =
    prettyNestedNew e1 <+> prettyNestedNew e2

  wlpretty (AppTy _ _ _ e1 t) =
    prettyNestedNew e1 <+> "@" <+> prettyNestedNew t

  wlpretty (Binop _ _ _ op e1 e2) =
    wlpretty e1 <+> wlpretty op <+> wlpretty e2

  wlpretty (LetDiamond _ _ _ v t e1 e2) =
    "let" <+> wlpretty v <+> ":" <> wlpretty t <+> "<-"
          <+> wlpretty e1 <+> "in" <+> wlpretty e2

  wlpretty (TryCatch _ _ _ e1 v t e2 e3) =
    "try" <+> wlpretty e1 <+> "as [" <> wlpretty v <> "]" <+> (if t /= Nothing then ":" <> wlpretty t else "") <+> "in"
          <+> wlpretty e2 <+> "catch" <+> wlpretty e3

  wlpretty (Val _ _ _ v) = wlpretty v
  wlpretty (Case _ _ _ e ps) = "\n    (case " <> wlpretty e <> " of\n      "
                      <> mconcat (P.punctuate ";\n      " (map (\(p, e') -> wlpretty p
                      <> " -> " <> wlpretty e') ps)) <> ")"
  wlpretty (Hole _ _ _ [] Nothing) = "?"
  wlpretty (Hole _ _ _ [] (Just hints)) = "{!" <> wlpretty hints <> " !}"
  wlpretty (Hole _ _ _ vs _) = "{!" <> P.sep (map wlpretty vs) <> "!}"

  wlpretty (Unpack _ _ _ tyVar var e1 e2) =
    "unpack <" <> wlpretty tyVar <> ", " <> wlpretty var <> "> = " <> wlpretty e1 <> " in " <> wlpretty e2

instance Pretty Operator where
  wlpretty = \case
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
prettyCompNew (var, Just ty) = wlpretty var <> " % " <> wlpretty ty
prettyCompNew (var, Nothing) = wlpretty var

instance Pretty Span where
  wlpretty
    | testing = const "(location redacted)"
    | otherwise = \case
      Span (0,0) _ "" -> "(unknown location)"
      Span (0,0) _ f  -> P.pretty f
      Span pos   _ f  -> P.pretty f <> ":" <> wlpretty pos

instance Pretty Pos where
    wlpretty (l, c) = P.pretty (show l) <> ":" <> P.pretty (show c)

instance Pretty Hints where
  wlpretty (Hints _ _ _ _ _ _)= ""
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
