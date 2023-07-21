module Language.Granule.Doc where

-- grdoc - Documentation generator

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Parser (parseDefs)
-- import Language.Granule.Syntax.Type
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Utils

import System.Directory
import System.FilePath
import Data.Text hiding
   (map, concatMap, filter, lines, take, takeWhile, dropWhile, drop, break, isPrefixOf, reverse)
import qualified Data.Text as Text

import Data.List (isPrefixOf, sort)
import Data.Version (showVersion)
import Paths_granule_interpreter (version)

import Control.Monad (when)

-- import Debug.Trace


-- Doc top-level
grDoc :: (?globals::Globals) => String -> AST () () -> IO ()
grDoc input ast = do
    createDirectoryIfMissing True "docs/modules"
    -- Run twice so that all the links are stable
    run True
    putStrLn "Rebuilding links."
    run False

  where

    -- Run with flag to say whether to show output or not
    run info = do
      -- Generate the file for this AST
      let modName = pretty $ moduleName ast
      when info $ putStrLn $ "Generate docs for " <> modName  <> "."
      moduleFile <- generateModulePage input ast
      -- create docs directory if its not there

      writeFile ("docs/modules/" <> modName <> ".html") (unpack moduleFile)
      -- Generate the Primitives file
      when info $ putStrLn $ "Generating docs index file."
      primFile <- generatePrimitivesPage
      writeFile "docs/modules/Primitives.html" (unpack primFile)
      -- Generate the index file
      indexFile <- generateIndexPage
      writeFile "docs/index.html" (unpack indexFile)
      return ()

data PageContext = IndexPage | ModulePage deriving (Eq, Show)

generateModulePage :: (?globals::Globals) => String -> AST () () -> IO Text
generateModulePage input ast =
    let modName = pack . pretty $ moduleName ast
    in generateModulePage' modName ("Module " <> modName) input ast

-- Generate module page from
--   module name
--   title for the page
--   input string
--   ast from that input
generateModulePage' :: (?globals::Globals) => Text -> Text -> String -> AST () () -> IO Text
generateModulePage' modName title input ast =
    generateFromTemplate ModulePage modName title content
   where
    inputLines = lines input
    content = (section "Meta-data" preamble)
           <> (section "Data types" (Text.concat dataDefs))
           <> (section "Definitions" (Text.concat defs))
    preamble = parsePreamble inputLines
    dataDefs = map (codeDiv . pack . pretty) (dataTypes ast)
    defs     = map prettyDef (definitions ast)
    prettyDef d =
         (codeDiv $ pack $ pretty (defId d) <> " : " <> pretty (defTypeScheme d))
      <> (descDiv $ scrapeDoc inputLines (defSpan d))

-- Generates the text of the index
generateIndexPage :: IO Text
generateIndexPage = do
  generateFromTemplate IndexPage "Index" "Welcome to Granule Docs!" indexText
   where
    indexText = "See links on the side for various modules."
             <> " Compiled with Granule version v" <> pack (showVersion version) <> "."

-- Generates the text of the primitives module
generatePrimitivesPage :: (?globals::Globals) => IO Text
generatePrimitivesPage = do
    generateModulePage' "Primitives" "Built-in primitives" (Primitives.builtinSrc) (fst . fromRight $ parseDefs "Primitives" Primitives.builtinSrc)
  where
    fromRight (Right x) = x
    fromRight (Left x)  = error x
generateFromTemplate :: PageContext -> Text -> Text -> Text -> IO Text
generateFromTemplate ctxt modName title content = do
  template <- readFile "docs/template.html"
  --
  template <- return $ pack template
  navigator <- generateNavigatorText ctxt
  return
      $ replace "MODULENAME"       modName
      $ replace "PATH_PREFIX"      (if ctxt == IndexPage then "" else "../")
      $ replace "<!--NAVIGATOR-->" navigator
      $ replace "<!--TITLE-->"     title
      $ replace "<!--CONTENT-->"   content template


generateNavigatorText :: PageContext -> IO Text
generateNavigatorText ctxt = do
  -- Get all module documentation files
  files <- getDirectoryContents "docs/modules"
  files <- return $ sort (filter (\file -> takeExtension file == ".html" && takeBaseName file /= "Primitives") files)
  -- Build a list of these links
  let prefix = if ctxt == ModulePage then "" else "modules/"
  let toLi file = li $ link (pack $ takeBaseName file) (prefix <> (pack $ takeBaseName file) <> ".html")
  -- Link to index page
  let indexPrefix = if ctxt == ModulePage then "../" else ""
  let topLevelLink = link "<i>Top-level</i><br />" (indexPrefix <> "index.html")
  let primitiveLink = toLi "Primitives"
  -- Build ul
  let list = map toLi files
  return $ topLevelLink <> ul (primitiveLink <> br <> Text.concat list)

-- Helpers for manipulating raw source

-- Scape comments preceding a particular point if they start with ---
scrapeDoc :: [String] -> Span -> Text
scrapeDoc inputLines span =
    Text.concat (reverse relevantLinesFormatted)
  where
    relevantLinesFormatted = map (pack . drop 3) relevantLines
    relevantLines = takeWhile ("--- " `isPrefixOf`) (dropWhile (== "") (reverse before))
    (before, _) = Prelude.splitAt (line - 1) inputLines
    (line, _) = startPos span


-- Parse the preamble from the front of a module file (if present)
parsePreamble :: [String] -> Text
parsePreamble inputLines =
    ul $ Text.concat (map presentPrequelLine prequelLines)
  where
    presentPrequelLine line =
        if name == "Module" -- drop duplicate module info
          then ""
          else li $ (tag "b" (pack name)) <> pack info
      where
       (name, info) = break (== ':') (drop 4 line)
    prequelLines =
      -- Not lines that are all "-" though
      filter (not . Prelude.all (== '-'))
      -- Only lines that start with "---"
      $ takeWhile (\line -> "---" `isPrefixOf` line) inputLines


---
-- HTML generation helpers

section :: Text -> Text -> Text
section "" contents   = tag "section" contents
section name contents = tag "section" (tag "h2" name <> contents)

codeDiv :: Text -> Text
codeDiv = tagWithAttributes "div" ("class='code'") . tag "pre"

descDiv :: Text -> Text
descDiv = tagWithAttributes "div" ("class='desc'")

span :: Text -> Text -> Text
span name = tagWithAttributes "span" ("class='" <> name <> "'")

ul :: Text -> Text
ul = tag "ul"

br :: Text
br = "<br />"

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