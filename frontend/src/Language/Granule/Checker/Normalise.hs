module Language.Granule.Checker.Normalise where

import Language.Granule.Syntax.Type
import Data.Functor.Identity (runIdentity)

normaliseType :: Type -> Type
normaliseType = runIdentity . typeFoldM (baseTypeFold { tfTyCase = reduceCase })
  where
    reduceCase t ps =
      case lookup t ps of
          Just t' -> return t'
          Nothing -> return $ TyCase t ps