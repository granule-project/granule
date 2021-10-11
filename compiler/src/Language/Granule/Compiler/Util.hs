-- | Utility functions for building Haskell expressions. Re-exports the
--   Haskell Src Exts helpers, and defines a few more.

module Language.Granule.Compiler.Util
  (
    module Language.Haskell.Exts
  , grImport
  , grPragmas
  , mkEquation
  , mkUnit
  ) where

import Language.Haskell.Exts

grImport :: ImportDecl ()
grImport = ImportDecl () (ModuleName () "Language.Granule.Runtime") False False False Nothing Nothing Nothing

grExts :: [Name ()]
grExts = map name ["GADTs", "ScopedTypeVariables", "Strict"]

mkPragmas :: [Name ()] -> ModulePragma ()
mkPragmas = LanguagePragma ()

grPragmas :: ModulePragma ()
grPragmas = mkPragmas grExts

mkEquation :: Name () -> [([Pat ()], Exp ())] -> Decl ()
mkEquation f bnds = FunBind () (map mkMatch bnds)
  where mkMatch :: ([Pat ()], Exp ()) -> Match ()
        mkMatch (pats,body) = Match () f pats (UnGuardedRhs () body) Nothing

mkUnit :: Type ()
mkUnit = TyCon () $ Special () $ UnitCon ()

-- > parseDecl "foo (x:xs) = 1"
-- ParseOk
-- (FunBind
--   [Match (Ident "foo")
--          [PParen (PInfixApp (PVar (Ident "x")) (Special (Cons)) (PVar (Ident "xs")))]
--          (UnGuardedRhs (Lit (Int 1 "1")))
--          Nothing])

-- > parseDecl "foo (F a) = 1\nfoo (G a) = 2"
-- ParseOk
--   (FunBind [Match (Ident "foo")
--                   [PParen (PApp (UnQual (Ident "F")) [PVar (Ident "a")])]
--                   (UnGuardedRhs (Lit (Int 1 "1"))) Nothing,
--             Match (Ident "foo")
--                   [PParen (PApp (UnQual (Ident "G")) [PVar (Ident "a")])]
--                   (UnGuardedRhs (Lit (Int 2 "2"))) Nothing])
