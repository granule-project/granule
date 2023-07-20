module Language.Granule.Doc where

-- grdoc - Documentation generator

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Pretty
-- import Language.Granule.Syntax.Type
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Utils

import System.Directory
import System.FilePath
import Data.Text hiding (map, concatMap, filter)
import qualified Data.Text as Text

import Data.Version (showVersion)
import Paths_granule_interpreter (version)


-- Doc top-level
grDoc :: (?globals::Globals) => AST () () -> IO ()
grDoc ast = do
  -- Generate the file for this AST
  let modName = pretty $ moduleName ast
  putStrLn $ "Generate docs for " <> modName  <> "."
  moduleFile <- generateModulePage ast
  writeFile ("docs/modules/" <> modName <> ".html") (unpack moduleFile)
  -- Generate the Primitives file
  putStrLn $ "Generating docs index file."
  primFile <- generatePrimitivesPage
  writeFile "docs/modules/Primitives.html" (unpack primFile)
  -- Generate the index file
  indexFile <- generateIndexPage
  writeFile "docs/index.html" (unpack indexFile)
  return ()

data PageContext = IndexPage | ModulePage deriving (Eq, Show)

generateModulePage :: (?globals::Globals) => AST () () -> IO Text
generateModulePage ast =
    let modName = pack . pretty $ moduleName ast
    in generateFromTemplate ModulePage modName ("Contexts of module " <> modName) content
   where
    content = Text.concat dataDefs <> Text.concat defs
    dataDefs = map (codeDiv . pack . pretty) (dataTypes ast)
    defs     = map (codeDiv . pack . prettyDef) (definitions ast)
    prettyDef d = pretty (defId d) <> " : " <> pretty (defTypeScheme d)

-- Generates the text of the index
generateIndexPage :: IO Text
generateIndexPage = do
  generateFromTemplate IndexPage "Index" "Welcome to Granule Docs!" indexText
   where
    indexText = "See links on the side for various modules."
             <> " Compile with version " <> pack (showVersion version) <> "\n."

-- Generates the text of the primitives module
generatePrimitivesPage :: (?globals::Globals) => IO Text
generatePrimitivesPage = do
  let prims = map (\(id, tys) -> codeDiv (pack $ pretty id <> " : " <> pretty tys)) Primitives.builtins
  generateFromTemplate ModulePage "Primitives" "Built-in primitives" (Text.concat prims)

generateFromTemplate :: PageContext -> Text -> Text -> Text -> IO Text
generateFromTemplate ctxt modName title content = do
  template <- readFile "docs/template.html"
  --
  template <- return $ pack template
  navigator <- generateNavigatorText ctxt
  return
      $ replace "MODULENAME"       modName
      $ replace "<!--NAVIGATOR-->" navigator
      $ replace "<!--TITLE-->"     title
      $ replace "<!--CONTENT-->"   content template


generateNavigatorText :: PageContext -> IO Text
generateNavigatorText ctxt = do
  -- Get all module documentation files
  files <- getDirectoryContents "docs/modules"
  files <- return $ filter (\file -> takeExtension file == ".html") files
  -- Build a list of these links
  let prefix = if ctxt == ModulePage then "" else "modules/"
  let toLi file = li $ link (pack $ takeBaseName file) (prefix <> (pack $ takeBaseName file) <> ".html")
  -- Link to index page
  let indexPrefix = if ctxt == ModulePage then "../" else ""
  let topLevelLink = link "<i>Top-level</i><br />" (indexPrefix <> "index.html")
  -- Build ul
  let list = map toLi files
  return $ topLevelLink <> ul (Text.concat list)

---
-- HTML generation helpers

codeDiv :: Text -> Text
codeDiv = tagWithAttributes "div" ("class='code'")

span :: Text -> Text -> Text
span name = tagWithAttributes "span" ("class='" <> name <> "'")

ul :: Text -> Text
ul = tag "ul"

li :: Text -> Text
li = tag "li"

-- link name href
link :: Text -> Text -> Text
link name href = "<a href='" <> href <> "'>" <> name <> "</a>"

tag :: Text -> Text -> Text
tag name content = "<" <> name <> ">" <> content <> "</" <> name <> ">"

tagWithAttributes :: Text -> Text -> Text -> Text
tagWithAttributes name attributes content =
  "<" <> name <> " " <> attributes <> ">" <> content <> "</" <> name <> ">"