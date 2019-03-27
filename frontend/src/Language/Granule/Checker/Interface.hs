{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
module Language.Granule.Checker.Interface
  ( getInterfaceMembers
  , getInterfaceParameters
  , getInterfaceParameterNames
  , getInterfaceParameterKinds
  , getInterfaceSigs
  , getInterfaceKind
  , getInterfaceConstraints
  , interfaceExists
  , registerInstanceSig
  , withInterfaceContext
  , buildBindingMap
  ) where


import Control.Monad.State (modify')
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.Map as M

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers (Id)
import Language.Granule.Syntax.Span (Span)
import Language.Granule.Syntax.Type

import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Instance
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(InstanceQ))
import Language.Granule.Checker.SubstitutionContexts

import Language.Granule.Utils (Globals)


ifaceCtxtNames :: IFaceCtxt -> [Id]
ifaceCtxtNames = map fst . ifaceSigs


-- | Type alias for a function that retrieves
-- | interface information from the state.
type RetFun a = (?globals :: Globals) => Span -> Id -> MaybeT Checker a


-- | Helper for retrieving interface information.
retFun :: (IFaceCtxt -> a) -> RetFun a
retFun f sp = fmap f . getInterface sp


interfaceExists :: Id -> MaybeT Checker Bool
interfaceExists = fmap (maybe False (const True)) . lookupContext ifaceContext


getInterface :: RetFun IFaceCtxt
getInterface = requireInScope (ifaceContext, "Interface")


getInterfaceParameters :: RetFun [(Id, Kind)]
getInterfaceParameters = retFun ifaceParams


-- | Helper for retrieving interface parameter information.
retFunParam :: ((Id, Kind) -> a) -> RetFun [a]
retFunParam f sp = fmap (fmap f) . getInterfaceParameters sp


getInterfaceParameterNames :: RetFun [Id]
getInterfaceParameterNames = retFunParam fst


getInterfaceParameterKinds :: RetFun [Kind]
getInterfaceParameterKinds = retFunParam snd


getInterfaceKind :: RetFun Kind
getInterfaceKind sp iname = do
  paramKinds <- getInterfaceParameterKinds sp iname
  pure $ foldr1 KFun (paramKinds <> [KConstraint InterfaceC])


getInterfaceSigs :: RetFun (Ctxt TypeScheme)
getInterfaceSigs = retFun ifaceSigs


getInterfaceMembers :: RetFun [Id]
getInterfaceMembers = retFun ifaceCtxtNames


getInterfaceConstraints :: RetFun [Inst]
getInterfaceConstraints = retFun ifaceConstraints


-- | Register an instantiated typescheme for an instance method.
registerInstanceSig :: Id -> InstanceTypes -> Id -> TypeScheme -> MaybeT Checker ()
registerInstanceSig iname (InstanceTypes _ ity) meth methTys =
    -- we lookup instances by the type application of the interface
    let finTy = mkInst iname ity
    in modify' $ \s -> s { instanceSigs = M.insert (finTy, meth) methTys (instanceSigs s) }


-- | Execute a checker with context from the interface head in scope.
withInterfaceContext :: (?globals :: Globals) => Span -> Id -> MaybeT Checker a -> MaybeT Checker a
withInterfaceContext sp iname c = do
  params <- getInterfaceParameters sp iname
  withBindings params InstanceQ c


-- | Build a substitution that maps interface parameter
-- | variables to the instance.
buildBindingMap :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker Substitution
buildBindingMap sp inst = do
  params <- getInterfaceParameterNames sp (instIFace inst)
  pure $ zip params (fmap (\p -> case p of
                                   (TyVar v) -> SubstK (KVar v)
                                   t -> SubstT t) (instParams inst))
