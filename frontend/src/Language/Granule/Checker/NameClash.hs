module Language.Granule.Checker.NameClash where

import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils

-- | Check if there are name clashes within namespaces
checkNameClashes :: AST () () -> Checker ()
checkNameClashes (AST dataDecls defs) =
    case concat [typeConstructorErrs, dataConstructorErrs, defErrs] of
      [] -> pure ()
      (d:ds) -> throwError (d:|ds)
  where
    typeConstructorErrs
      = fmap mkTypeConstructorErr
      . duplicatesBy (sourceId . dataDeclId)
      $ dataDecls

    mkTypeConstructorErr (x2, xs)
      = NameClashTypeConstructors
          { errLoc = dataDeclSpan x2
          , errDataDecl = x2
          , otherDataDecls = xs
          }

    dataConstructorErrs
      = fmap mkDataConstructorErr                -- make errors for duplicates
      . duplicatesBy (sourceId . dataConstrId)   -- get the duplicates by source id
      . concatMap dataDeclDataConstrs            -- get data constructor definitions
      $ dataDecls                                -- from data declarations

    mkDataConstructorErr (x2, xs)
      = NameClashDataConstructors
          { errLoc = dataConstrSpan x2
          , errDataConstructor = x2
          , otherDataConstructors = xs
          }

    defErrs
      = fmap mkDuplicateDefErr
      . duplicatesBy (sourceId . defId)
      $ defs

    mkDuplicateDefErr (x2, xs)
      = NameClashDefs
          { errLoc = defSpan x2
          , errDef = x2
          , otherDefs = xs
          }