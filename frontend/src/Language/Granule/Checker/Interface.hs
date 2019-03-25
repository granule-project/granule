module Language.Granule.Checker.Interface
  ( getInterfaceMembers
  , getInterfaceParameters
  , getInterfaceParameterNames
  , getInterfaceParameterKinds
  , getInterfaceSigs
  , getInterfaceKind
  , getInterfaceConstraints
  , registerInstanceSig
  , withInterfaceContext
  , buildBindingMap
  ) where


import Control.Monad.State (modify')
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.Map as M

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers (Id)
import Language.Granule.Syntax.Type

import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Instance
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(InstanceQ))
import Language.Granule.Checker.SubstitutionContexts


ifaceCtxtNames :: IFaceCtxt -> [Id]
ifaceCtxtNames = map fst . ifaceSigs


getInterface :: Id -> MaybeT Checker (Maybe IFaceCtxt)
getInterface = lookupContext ifaceContext


getInterfaceParameters :: Id -> MaybeT Checker (Maybe [(Id, Kind)])
getInterfaceParameters = fmap (fmap ifaceParams) . getInterface


getInterfaceParameterNames :: Id -> MaybeT Checker (Maybe [Id])
getInterfaceParameterNames = fmap (fmap (fmap fst)) . getInterfaceParameters


getInterfaceParameterKinds :: Id -> MaybeT Checker (Maybe [Kind])
getInterfaceParameterKinds = fmap (fmap (fmap snd)) . getInterfaceParameters


getInterfaceKind :: Id -> MaybeT Checker (Maybe Kind)
getInterfaceKind iname = do
  paramKinds <- fmap (fmap $ fmap snd) $ getInterfaceParameters iname
  pure $ fmap (\pkinds -> foldr1 KFun (pkinds <> [KConstraint InterfaceC])) paramKinds


getInterfaceSigs :: Id -> MaybeT Checker (Maybe (Ctxt TypeScheme))
getInterfaceSigs = fmap (fmap ifaceSigs) . getInterface


getInterfaceMembers :: Id -> MaybeT Checker (Maybe [Id])
getInterfaceMembers = fmap (fmap ifaceCtxtNames) . getInterface


getInterfaceConstraints :: Id -> MaybeT Checker (Maybe [Inst])
getInterfaceConstraints = fmap (fmap ifaceConstraints) . getInterface


-- | Register an instantiated typescheme for an instance method.
registerInstanceSig :: Id -> InstanceTypes -> Id -> TypeScheme -> MaybeT Checker ()
registerInstanceSig iname (InstanceTypes _ ity) meth methTys =
    -- we lookup instances by the type application of the interface
    let finTy = mkInst iname ity
    in modify' $ \s -> s { instanceSigs = M.insert (finTy, meth) methTys (instanceSigs s) }


-- | Execute a checker with context from the interface head in scope.
withInterfaceContext :: Id -> MaybeT Checker a -> MaybeT Checker a
withInterfaceContext iname c = do
  Just params <- getInterfaceParameters iname
  withBindings params InstanceQ c


-- | Build a substitution that maps interface parameter
-- | variables to the instance.
buildBindingMap :: Inst -> MaybeT Checker Substitution
buildBindingMap inst = do
  Just params <- getInterfaceParameterNames (instIFace inst)
  pure $ zip params (fmap SubstT (instParams inst))
