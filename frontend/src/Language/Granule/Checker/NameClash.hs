module Language.Granule.Checker.NameClash where

import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Utils

-- | Check if there are name clashes within namespaces
checkNameClashes :: AST () () -> Checker ()
checkNameClashes (AST dataDecls defs ifaces _ _) =
    case concat [typeConstructorErrs, dataConstructorErrs, defErrs] of
      [] -> pure ()
      (d:ds) -> throwError (d:|ds)
  where
    typeConstructorErrs
      = fmap mkTypeConstructorErr
      . duplicatesBy (sourceName . tyConId)
      $ fmap Right dataDecls <> fmap Left ifaces
      where tyConId = either interfaceId dataDeclId

    mkTypeConstructorErr (x2, xs)
      = NameClashTypeConstructors
          { errLoc = tyConSpan x2
          , errTyCon = x2
          , otherTyCons = xs
          }
        where tyConSpan = either interfaceSpan dataDeclSpan

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
