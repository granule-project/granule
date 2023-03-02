-- | Check if there are name clashes within namespaces
module Language.Granule.Checker.NameClash where

import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Utils

checkNameClashes :: AST () () -> Checker ()
checkNameClashes AST{ dataTypes = dataDecls, definitions = defs } =
    case concat [typeConstructorErrs, dataConstructorErrs, defErrs] of
      [] -> pure ()
      (d:ds) -> throwError (d:|ds)
  where
    typeConstructorErrs
      = fmap mkTypeConstructorErr
      . duplicatesBy (sourceName . dataDeclId)
      $ dataDecls

    mkTypeConstructorErr (x2, xs)
      = NameClashTypeConstructors
          { errLoc = dataDeclSpan x2
          , errDataDecl = x2
          , otherDataDecls = xs
          }

    dataConstructorErrs
      = fmap mkDataConstructorErr                -- make errors for duplicates
      . duplicatesBy (sourceName . dataConstrId)   -- get the duplicates by source id
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
      . duplicatesBy (sourceName . defId)
      $ defs

    mkDuplicateDefErr (x2, xs)
      = NameClashDefs
          { errLoc = defSpan x2
          , errDef = x2
          , otherDefs = xs
          }
