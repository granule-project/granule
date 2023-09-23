-- | Check if there are name clashes within namespaces
module Language.Granule.Checker.NameClash where

import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Utils
import qualified Language.Granule.Checker.Primitives as Primitives

checkNameClashes :: (?globals :: Globals)
                 => [(Id, (Type, [Id], [Int]))] -> [DataDecl] -> AST () () -> AST () () -> Checker ()
checkNameClashes typeConstructors builtinDataDecls (AST dataDecls defs _ _ _) builtinsAST =
    case concat [typeConstructorErrs, dataConstructorErrs, defErrs] of
      []     -> pure ()
      (d:ds) -> throwError (d:|ds)
  where
    dataDecls' = builtinDataDecls
              <> dataDecls
             <> tcsAsDataDecls
                       (filter (\x -> not (fst x `elem` Primitives.overlapsAllowed)) typeConstructors)

    typeConstructorErrs
      = fmap mkTypeConstructorErr
      . duplicatesBy (sourceName . dataDeclId)
      $ dataDecls'

    -- From a list of built-type constructors, make them into dummy data type definitions for this check
    tcsAsDataDecls = map toDataDecl
      where
        span = nullSpan {filename = "primitive"}
        toDataDecl (id, (kind, dataConstrNames, _)) =
          DataDecl span id [] (Just kind) (map toDataConsDecl dataConstrNames)
        toDataConsDecl id = DataConstrNonIndexed span id []

    mkTypeConstructorErr (x2, xs)
      = NameClashTypeConstructors
          { errLoc = dataDeclSpan x2
          , errDataDecl = x2
          , otherDataDecls = xs
          }

    dataConstructorErrs
      = fmap mkDataConstructorErr                -- make errors for duplicates
      . duplicatesBy (sourceName . dataConstrId) -- get the duplicates by source id
      . concatMap dataDeclDataConstrs            -- get data constructor definitions
      $ dataDecls'                               -- from data declarations

    mkDataConstructorErr (x2, xs)
      = NameClashDataConstructors
          { errLoc = dataConstrSpan x2
          , errDataConstructor = x2
          , otherDataConstructors = xs
          }

    defErrs
      = fmap mkDuplicateDefErr
      . duplicatesBy (sourceName . defId)
      $ (defs ++ definitions builtinsAST)



    mkDuplicateDefErr (x2, xs)
      = NameClashDefs
          { errLoc = defSpan x2
          , errDef = x2
          , otherDefs = xs
          }