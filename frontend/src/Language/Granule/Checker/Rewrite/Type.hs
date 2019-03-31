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
      -- ** Environment
    , RewriteEnv
    , buildRewriterEnv
    , getEnv
    , InstanceId
    , mkInstanceId
    , typeConstructors
    , dataConstructors
      -- * Error system
    , RewriterError
    , genericRewriterError
    , illFormedEnvError
      -- * Helpers
    , registerInterface
    , isInterfaceVar
    , getInstanceMethTys
    , registerDef
    , lookupDef
    , expandConstraints
    , registerIFun
    , lookupIfaceIfuns
    ) where


import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.State (MonadState, StateT, evalStateT, get, modify')
import qualified Data.Map as M

import Language.Granule.Context (Ctxt)
import qualified Language.Granule.Context as Ctxt
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Instance
import Language.Granule.Checker.SubstitutionContexts (Substitution)


--------------------------
----- Rewriter Monad -----
--------------------------


-----------
-- State --
-----------


type DefMap = Ctxt (Def () ())


-- | A mapping from interface names to their
-- | dictionary instances.
type IFunMap = M.Map Id [(Inst, Def () ())]


data RewriteState = RewriteState {
      rsDefMap :: DefMap
    , rsIFaces :: [Id]
    , rsInstFuns :: IFunMap
    }


startRewriteState :: RewriteState
startRewriteState = RewriteState Ctxt.empty [] M.empty


modifyDefs :: (DefMap -> DefMap) -> Rewriter ()
modifyDefs f = modify' $ \s -> s { rsDefMap = f (rsDefMap s) }


getDefMap :: Rewriter DefMap
getDefMap = fmap rsDefMap get


modifyInterfaces :: ([Id] -> [Id]) -> Rewriter ()
modifyInterfaces f = modify' $ \s -> s { rsIFaces = f (rsIFaces s) }


getInterfaces :: Rewriter [Id]
getInterfaces = fmap rsIFaces get


modifyInstFuns :: (IFunMap -> IFunMap) -> Rewriter ()
modifyInstFuns f = modify' $ \s -> s { rsInstFuns = f (rsInstFuns s) }


-----------------
-- Environment --
-----------------


-- | Unique identifier for an instance.
-- |
-- | This is the application of an interface type
-- | constructor to an instance type.
type InstanceId = Inst


mkInstanceId :: Instance v a -> InstanceId
mkInstanceId (Instance _ iname _ (InstanceTypes _ idt) _) = mkInst iname idt


type TyConsContext = Ctxt (Kind, Cardinality)


type DataConsContext = Ctxt (TypeScheme, Substitution)


-- | Environment produced from type checking.
data RewriteEnv = RewriteEnv {
    -- ^ Instantiated type signatures for instances.
    instanceSignatures :: [((InstanceId, Id), TypeScheme)]
  , expandedConstraints :: Ctxt [Inst]
  , typeConstructors :: TyConsContext
  , dataConstructors :: DataConsContext
  }


-- | Retrieve the environment of the rewriter.
getEnv :: Rewriter RewriteEnv
getEnv = ask


type RewriterError = String


-- TODO: Remove IO from the Rewriter (GuiltyDolphin --- 2019-03-02)
-- - this only has IO so that we can run some Checker stuff
--   (such as substitutions) inside the rewriter - if we remove
--   the need for IO from the Checker, or generalise substitutions
--   so that they don't rely upon the checker, then we should be
--   able to remove IO from this)
newtype Rewriter v = Rewriter
    { unRewriter :: ExceptT RewriterError
                    (ReaderT RewriteEnv
                     (StateT RewriteState IO)) v }
    deriving (Functor, Applicative, Monad,
              MonadError RewriterError,
              MonadReader RewriteEnv,
              MonadState RewriteState,
              MonadIO)


execRewriter :: Rewriter v -> RewriteEnv -> RewriteState -> IO (Either RewriterError v)
execRewriter r = evalStateT . runReaderT (runExceptT (unRewriter r))


-- | Run a new rewriter with the given input environment.
runNewRewriter :: Rewriter v -> RewriteEnv -> IO (Either RewriterError v)
runNewRewriter r renv = execRewriter r renv startRewriteState


-- | Build an environment for the rewriter.
buildRewriterEnv :: [((InstanceId, Id), TypeScheme)]
                 -> Ctxt [Inst]
                 -> TyConsContext
                 -> DataConsContext
                 -> RewriteEnv
buildRewriterEnv = RewriteEnv


------------
-- Errors --
------------


genericRewriterError :: String -> Rewriter a
genericRewriterError = throwError


illFormedEnvError :: Rewriter a
illFormedEnvError = genericRewriterError "rewriter received an illformed environment"


-------------------
----- Helpers -----
-------------------


getInstanceSignatures :: Rewriter [((InstanceId, Id), TypeScheme)]
getInstanceSignatures = fmap instanceSignatures ask


getInstanceMethTys :: InstanceId -> Id -> Rewriter TypeScheme
getInstanceMethTys instId methName = do
  allSigs <- getInstanceSignatures
  maybe illFormedEnvError pure (lookup (instId, methName) allSigs)


registerDef :: Def () () -> Rewriter ()
registerDef def@(Def _ n _ _) = modifyDefs ((n,def):)


lookupDef :: Id -> Rewriter (Maybe (Def () ()))
lookupDef n = fmap (lookup n) getDefMap


registerInterface :: Id -> Rewriter ()
registerInterface iname = modifyInterfaces (iname:)


-- | True if the given id represents an interface in scope.
isInterfaceVar :: Id -> Rewriter Bool
isInterfaceVar n = fmap (elem n) getInterfaces


getExpandedConstraints :: Rewriter (Ctxt [Inst])
getExpandedConstraints = fmap expandedConstraints ask


expandConstraints :: Id -> Rewriter [Inst]
expandConstraints n = do
  exps <- getExpandedConstraints
  maybe illFormedEnvError pure (lookup n exps)


registerIFun :: Id -> InstanceTypes -> Def () () -> Rewriter ()
registerIFun n (InstanceTypes _ idt) def = modifyInstFuns (M.insertWith (<>) n [(mkInst n idt, def)])


lookupIfaceIfuns :: Id -> Rewriter (Maybe [(Inst, Def () ())])
lookupIfaceIfuns n = fmap (M.lookup n . rsInstFuns) get
