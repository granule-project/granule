{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Interface
  ( getKindRequired
  , getInterfaceMembers
  , getInterfaceParameters
  , getInterfaceParameterNames
  , getInterfaceParameterKinds
  , getInterfaceSig
  , getInterfaceKind
  , getInterfaceConstraints
  , registerInstanceSig
  ) where


import Control.Monad (join)
import Control.Monad.State (modify')
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.Map as M

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers (Id)
import Language.Granule.Syntax.Pretty (pretty)
import Language.Granule.Syntax.Span (Span)
import Language.Granule.Syntax.Type

import Language.Granule.Context (Ctxt)
import Language.Granule.Utils (Globals)

import Language.Granule.Checker.Errors
import Language.Granule.Checker.Instance
import Language.Granule.Checker.Monad


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


getInterfaceSig :: Id -> Id -> MaybeT Checker (Maybe TypeScheme)
getInterfaceSig iname name = fmap join $ fmap (fmap $ lookup name) (getInterfaceSigs iname)


getInterfaceConstraints :: Id -> MaybeT Checker (Maybe [Inst])
getInterfaceConstraints = fmap (fmap ifaceConstraints) . getInterface


-- | Retrieve a kind from the type constructor scope
getKindRequired :: (?globals :: Globals) => Span -> Id -> MaybeT Checker Kind
getKindRequired sp name = do
  ikind <- getInterfaceKind name
  case ikind of
    Just k -> pure k
    Nothing -> do
      tyCon <- lookupContext typeConstructors name
      case tyCon of
        Just (kind, _) -> pure kind
        Nothing -> do
          dConTys <- requireInScope (dataConstructors, "Interface or constructor") sp name
          case dConTys of
            (Forall _ [] [] t, []) -> pure $ KPromote t
            _ -> halt $ GenericError (Just sp)
                 ("I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty name)


-- | Register an instantiated typescheme for an instance method.
registerInstanceSig :: Id -> InstanceTypes -> Id -> TypeScheme -> MaybeT Checker ()
registerInstanceSig iname (InstanceTypes _ ity) meth methTys =
    -- we lookup instances by the type application of the interface
    let finTy = mkInst iname ity
    in modify' $ \s -> s { instanceSigs = M.insert (finTy, meth) methTys (instanceSigs s) }
