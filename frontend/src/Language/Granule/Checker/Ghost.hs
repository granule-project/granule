{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}

module Language.Granule.Checker.Ghost where

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Monad

import Data.List (partition)
import Language.Granule.Utils

allGhostVariables :: Ctxt Assumption -> Ctxt Assumption
allGhostVariables = filter isGhost

-- | Default (singleton) ghost variable context
freshGhostVariableContext :: (?globals :: Globals) => Ctxt Assumption
freshGhostVariableContext =
  [(mkId ghostName, Ghost defaultGhost) | SecurityLevels `elem` globalsExtensions ?globals]

-- | (Singleton) ghost variable context where the ghost is used
usedGhostVariableContext :: (?globals :: Globals) => Ctxt Assumption
usedGhostVariableContext =
  [(mkId ghostName, Ghost (TyGrade (Just $ tyCon "Level") 1)) | SecurityLevels `elem` globalsExtensions ?globals]

-- | (Singleton) ghost variable context where the ghost is unused
weakenedGhostVariableContext :: (?globals :: Globals) => Ctxt Assumption
weakenedGhostVariableContext =
  [(mkId ghostName, Ghost (TyGrade (Just $ tyCon "Level") 0)) | SecurityLevels `elem` globalsExtensions ?globals]

ghostVariableContextMeet :: (?globals :: Globals) => Ctxt Assumption -> Checker (Ctxt Assumption)
ghostVariableContextMeet env =
  if SecurityLevels `elem` globalsExtensions ?globals
  then return env
  else let (ghosts,env') = partition isGhost env
           newGrade = foldr1 converge $ map ((\(Ghost ce) -> ce) . snd) ghosts
           -- if there's no ghost variable in env, don't add one
       in if null ghosts then return env' else return $ (mkId ghostName, Ghost newGrade) : env'

isGhost :: (a, Assumption) -> Bool
isGhost (_, Ghost _) = True
isGhost _ = False

defaultGhost :: Coeffect
defaultGhost = tyCon "Dunno"

unprotectedGhost :: Coeffect
unprotectedGhost = tyCon "Private"

unprotectedGhostVariableContext :: (?globals :: Globals) => Ctxt Assumption
unprotectedGhostVariableContext =
  [(mkId ghostName, Ghost unprotectedGhost) | SecurityLevels `elem` globalsExtensions ?globals]

ghostOp :: TypeOperator
ghostOp = TyOpConverge

-- do converge operator
converge :: Coeffect -> Coeffect -> Coeffect
converge = TyInfix ghostOp

ghostName :: String
ghostName = ".var.ghost"
