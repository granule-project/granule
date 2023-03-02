-- | How Granule programs are structured into Modules

module Language.Granule.Syntax.Program
  ( module Language.Granule.Syntax.Program
  , module Reexport
  )
where

import Language.Granule.Utils
import Language.Granule.Syntax.Def as Reexport
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Preprocessor

import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import Data.Time.Clock (UTCTime)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative (empty)
import System.FilePath ((<.>))
import Control.Exception (try)

-- | Invariants:
-- * rootModule \in modules
-- if a Module has a module signature, then it is assumed that type checking can be skipped
data GranuleProgram = GranulePrg
  { rootModule :: ModuleName
  , modules :: Map ModuleName Module
  , dependencyGraph :: AdjacencyMap ModuleName
  }

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
  { dataDeclarationContext :: Ctxt DataDecl
  , definitionContext :: Ctxt TypeScheme
  , derivedDefinitions :: [Def () ()]
  }

type E = String

readAndPreprocessGranuleProgram :: (?globals :: Globals)
  => FilePath
  -> IO (Either E GranuleProgram)
readAndPreprocessGranuleProgram filePath = do
  src <- preprocess filePath
  rootModule <- parseModule src
  let ?gloabals = ?globals { globalsRewriter = Nothing }
  moduleImports rootModule


goImports :: (?globals :: Globals)
  => Module
  -> Set ModuleName
  -> IO (Either E [(ModuleName, ModuleName)])
goImports rootModule imports = do
  let (foo :: _) = traverse (try . readFile) [fp <.> ext | ext <- granuleFileTypes]
  undefined

granuleFileTypes = ["gr", "gr.md", "gr.tex", "gr.latex"]



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
