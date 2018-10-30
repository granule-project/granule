module Syntax.Freshening where

import Data.List (delete)
import Control.Monad.Trans.State.Strict

import Syntax.Identifiers

-- | Natural numbers
type Nat = Word

class Freshenable t where
  -- Alpha-convert bound variables to avoid name capturing
  freshen :: t -> Freshener t

class Term t where
  -- Compute the free variables in an open term
  freeVars :: t -> [Id]

-- Used to distinguish the value-level and type-level variables
data IdSyntacticCategory = Value | Type


-- | The freshening monad for alpha-conversion to avoid name capturing
type Freshener t = State FreshenerState t

data FreshenerState = FreshenerState
  { counter :: Nat -- ^ fresh Id counter
  , varMap :: [(String, String)] -- ^ mapping of variables to their fresh names
  , tyMap  :: [(String, String)] -- ^ mapping of type variables to fresh names
  } deriving Show

-- | Given something freshenable,
-- | e.g. the AST, run the freshener on it and return the final state
-- >>> runFreshener (PVar ((0,0),(0,0)) (Id "x" "x"))
-- PVar ((0,0),(0,0)) (Id "x" "x_0")
runFreshener :: Freshenable t => t -> t
runFreshener x = evalState (freshen x) FreshenerState { counter = 0, varMap = [], tyMap = [] }

removeFreshenings :: [Id] -> Freshener ()
removeFreshenings [] = return ()
removeFreshenings (x:xs) = do
    st <- get
    put st { varMap = delete x' (varMap st) }
    removeFreshenings xs
  where
    x' = (sourceName x, internalName x)

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshVar :: IdSyntacticCategory -> Id -> Freshener Id
freshVar cat var = do
    st <- get
    let var' = sourceName var <> "_" <> show (counter st)
    case cat of
      Value -> put st { counter = (counter st) + 1, varMap = (sourceName var, var') : (varMap st) }
      Type  -> put st { counter = (counter st) + 1,  tyMap = (sourceName var, var') :  (tyMap st) }
    return var { internalName = var' }

-- | Look up a variable in the freshener state.
-- If @Nothing@ then the variable name shouldn't change
lookupVar :: IdSyntacticCategory -> Id -> Freshener (Maybe String)
lookupVar cat v = do
  st <- get
  case cat of
    Value -> return . lookup (sourceName v) . varMap $ st
    Type  -> return . lookup (sourceName v) .  tyMap $ st
