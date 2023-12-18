-- | How Granule programs are structured into Modules

module Language.Granule.Syntax.Program
  ( module Language.Granule.Syntax.Program
  , module Reexport
  )
where

import Language.Granule.Utils
import Language.Granule.Syntax.Def as Reexport
import Language.Granule.Syntax.Type

import Algebra.Graph.AdjacencyMap (AdjacencyMap)
-- import Data.Time.Clock (UTCTime)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative (empty)


-- | Invariants:
-- * rootModule \in modules
-- if a Module has a module signature, then it is assumed that type checking can be skipped
data GranuleProgram = GranulePrg
  { granulePrgRootModule :: ModuleName
  , granulePrgModules :: Map ModuleName Module
  , granulePrgDependencyGraph :: AdjacencyMap ModuleName
  }
  deriving (Show, Eq)

type ModuleName = String

data Module = Mod
  { moduleAST :: AST () ()
  , moduleName :: ModuleName
  -- , moduleMetadata :: ModuleMetadata
  , moduleExtensions :: Set Extension
  , moduleSignature :: Maybe ModuleSignature
  , moduleImports :: Set ModuleName
  , moduleHiddenNames :: Map Id ModuleName -- map from names to the module hiding them
  }
  deriving (Show, Eq)

emptyModule :: Module
emptyModule = Mod
  { moduleAST = emptyAST
  , moduleName = empty
  -- , moduleMetadata = emptyModuleMetadata
  , moduleExtensions = Set.empty
  , moduleSignature = empty
  , moduleImports = Set.empty
  , moduleHiddenNames = Map.empty
  }

-- data ModuleMetadata = ModMeta
--   { moduleMetaFilePath :: Maybe FilePath -- a module might not have a filepath, or we might not even have a module source at all and just run the type checker on the signature (with --no-eval)
--   , moduleMetaFileModificationTime :: Maybe UTCTime
--   , moduleMetaSignatureFilePath :: Maybe FilePath
--   , moduleMetaSignatureFileModificationTime :: Maybe UTCTime
--   }

-- emptyModuleMetadata :: ModuleMetadata
-- emptyModuleMetadata =
--   ModMeta
--     { moduleMetaFilePath = empty
--     , moduleMetaFileModificationTime = empty
--     , moduleMetaSignatureFilePath = empty
--     , moduleMetaSignatureFileModificationTime = empty
--     }

data ModuleSignature = ModSig
  { modSigDataDeclarationContext :: Ctxt DataDecl
  , modSigDefinitionContext :: Ctxt TypeScheme
  , modSigDerivedDefinitions :: [Def () ()]
  }
  deriving (Show, Eq)

emptyModuleSignature :: ModuleSignature
emptyModuleSignature = ModSig
  { modSigDataDeclarationContext = empty
  , modSigDefinitionContext = empty
  , modSigDerivedDefinitions = empty
  }


-- fileLocal <- doesFileExist i
--           let path = if fileLocal then i else includePath </> i
--           let ?globals = ?globals { globalsSourceFilePath = Just path } in do
--             src <- readFile path
--             (AST dds' defs' imports' hidden' _, extensions') <- either failWithMsg return $ parseDefs path src
--             doImportsRecursively
--               (fromList todo <> imports')
--               ( AST (dds' <> dds) (defs' <> defs) (insert i done) (hidden `M.union` hidden') name
--               , extensions ++ extensions'
--               )
