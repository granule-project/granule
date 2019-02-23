{- |
Module      :  Language.Granule.Checker.Rewrite.Type
Description :  Types for the rewriter

Contains types and helpers for the rewriter.
-}


{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Checker.Rewrite.Type
    ( -- * Rewriter Monad
      Rewriter
    , runNewRewriter
    , RewriteEnv
    , buildRewriterEnv
    , InstanceId
    , mkInstanceId
      -- * Error system
    , RewriterError
    , illFormedEnvError
      -- * Helpers
    , getInstanceMethTys
    ) where


import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.State (MonadState, State, evalState)

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type


--------------------------
----- Rewriter Monad -----
--------------------------


type RewriteState = String


startRewriteState :: RewriteState
startRewriteState = ""


-- | Unique identifier for an instance.
-- |
-- | This is the application of an interface type
-- | constructor to an instance type.
type InstanceId = Type


mkInstanceId :: Instance v a -> InstanceId
mkInstanceId (Instance _ iname _ (IFaceDat _ ty) _) = TyApp (TyCon iname) ty


newtype RewriteEnv = RewriteEnv {
      -- ^ Instantiated type signatures for instances.
      instanceSignatures :: [((InstanceId, Id), TypeScheme)]
      }


type RewriterError = String


-- newtype Rewriter v = Rewriter { unRewriter :: State RewriteState v }
newtype Rewriter v = Rewriter
    { unRewriter :: ExceptT RewriterError
                    (ReaderT RewriteEnv
                     (State RewriteState)) v }
    deriving (Functor, Applicative, Monad,
              MonadError RewriterError,
              MonadReader RewriteEnv,
              MonadState RewriteState)


execRewriter :: Rewriter v -> RewriteEnv -> RewriteState -> Either RewriterError v
execRewriter r = evalState . runReaderT (runExceptT (unRewriter r))


-- | Run a new rewriter with the given input environment.
runNewRewriter :: Rewriter v -> RewriteEnv -> Either RewriterError v
runNewRewriter r renv = execRewriter r renv startRewriteState


-- | Build an environment for the rewriter.
buildRewriterEnv :: [((InstanceId, Id), TypeScheme)] -> RewriteEnv
buildRewriterEnv = RewriteEnv


------------
-- Errors --
------------


illFormedEnvError :: Rewriter a
illFormedEnvError = throwError "rewriter received an illformed environment"


-------------------
----- Helpers -----
-------------------


getInstanceSignatures :: Rewriter [((InstanceId, Id), TypeScheme)]
getInstanceSignatures = fmap instanceSignatures ask


getInstanceMethTys :: InstanceId -> Id -> Rewriter TypeScheme
getInstanceMethTys instId methName = do
  allSigs <- getInstanceSignatures
  maybe illFormedEnvError pure (lookup (instId, methName) allSigs)
