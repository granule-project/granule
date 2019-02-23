{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Interface
  ( getKindRequired
  , getInterfaceMembers
  , getInterfaceParameter
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
import Language.Granule.Syntax.Span (Span)
import Language.Granule.Syntax.Type

import Language.Granule.Context (Ctxt)
import Language.Granule.Utils (Globals)

import Language.Granule.Checker.Monad


ifaceCtxtNames :: IFaceCtxt -> [Id]
ifaceCtxtNames = map fst . ifaceSigs


getInterface :: Id -> MaybeT Checker (Maybe IFaceCtxt)
getInterface = lookupContext ifaceContext


getInterfaceParameter :: Id -> MaybeT Checker (Maybe Id)
getInterfaceParameter = fmap (fmap ifaceParam) . getInterface


getInterfaceKind :: Id -> MaybeT Checker (Maybe Kind)
getInterfaceKind = fmap (fmap $ ifaceParamKind) . getInterface


getInterfaceSigs :: Id -> MaybeT Checker (Maybe (Ctxt TypeScheme))
getInterfaceSigs = fmap (fmap ifaceSigs) . getInterface


getInterfaceMembers :: Id -> MaybeT Checker (Maybe [Id])
getInterfaceMembers = fmap (fmap ifaceCtxtNames) . getInterface


getInterfaceSig :: Id -> Id -> MaybeT Checker (Maybe TypeScheme)
getInterfaceSig iname name = fmap join $ fmap (fmap $ lookup name) (getInterfaceSigs iname)


getInterfaceConstraints :: Id -> MaybeT Checker (Maybe [Type])
getInterfaceConstraints = fmap (fmap ifaceConstraints) . getInterface


-- | Retrieve a kind from the type constructor scope
getKindRequired :: (?globals :: Globals) => Span -> Id -> MaybeT Checker Kind
getKindRequired sp name = do
  ikind <- getInterfaceKind name
  case ikind of
    Just k -> pure (KFun k (KConstraint Interface))
    Nothing -> do
      tyCon <- lookupContext typeConstructors name
      case tyCon of
        Just (kind, _) -> pure kind
        Nothing -> do
          dConTys <- requireInScope (dataConstructors, "Constructor") sp name
          case dConTys of
            (Forall _ [] [] t, []) -> pure $ KPromote t
            _ -> halt $ GenericError (Just s)
                 ("I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty name)


-- | Register an instantiated typescheme for an instance method.
registerInstanceSig :: Id -> IFaceDat -> Id -> TypeScheme -> MaybeT Checker ()
registerInstanceSig iname (IFaceDat _ ity) meth methTys =
    -- we lookup instances by the type application of the interface
    let finTy = TyApp (TyCon iname) ity
    in modify' $ \s -> s { instanceSigs = M.insert (finTy, meth) methTys (instanceSigs s) }
