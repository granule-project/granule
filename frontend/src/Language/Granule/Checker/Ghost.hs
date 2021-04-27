{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}

module Language.Granule.Checker.Ghost where

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Monad

import Data.List (partition)

allGhostVariables :: Ctxt Assumption -> Ctxt Assumption
allGhostVariables = filter isGhost

freshGhostVariableContext :: Checker (Ctxt Assumption)
freshGhostVariableContext = do
  return [(mkId ghostName,
           Ghost defaultGhost)]
           -- Ghost (TyGrade Nothing 0))]

ghostVariableContextMeet :: Ctxt Assumption -> Checker (Ctxt Assumption)
ghostVariableContextMeet env =
  -- let (ghosts,env') = partition isGhost env
  --     newGrade      = foldr (TyInfix TyOpMeet) (tyCon "Unused") $ map ((\(Ghost ce) -> ce) . snd) ghosts
  -- in return $ (mkId ".var.ghost", Ghost newGrade) : env'
  let (ghosts,env') = partition isGhost env
      newGrade = foldr1 converge $ map ((\(Ghost ce) -> ce) . snd) ghosts
  -- if there's no ghost variable in env, don't add one
  in if null ghosts then return env' else return $ (mkId ghostName, Ghost newGrade) : env'

isGhost :: (a, Assumption) -> Bool
isGhost (_, Ghost _) = True
isGhost _ = False

defaultGhost :: Coeffect
-- defaultGhost = TyGrade (Just $ tyCon "Level") 3 -- dunno label
defaultGhost = TyGrade (Just $ tyCon "Level") 0
-- defaultGhost = TyGrade Nothing 0

ghostOp :: TypeOperator
ghostOp = TyOpConverge

converge :: Coeffect -> Coeffect -> Coeffect
converge (TyGrade (Just k) 0) (TyGrade (Just _k) 0) = TyGrade (Just k) 0
converge c1 c2 = TyInfix ghostOp c1 c2

ghostName :: String
ghostName = ".var.ghost"
