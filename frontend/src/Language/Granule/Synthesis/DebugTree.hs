{-# options_ghc -fno-warn-unused-imports #-}
module Language.Granule.Synthesis.DebugTree where

import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Pretty as P 

import Language.Granule.Context

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span

import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Contexts
import Language.Granule.Synthesis.Common
import Language.Granule.Utils

import System.FilePath ((-<.>))



pathToHtml :: (?globals :: Globals) => RuleInfo -> Html 
pathToHtml path = 
  docTypeHtml $ do 
    H.head $ do 
      H.title $ toHtml "Synthesis output"
    -- 
    body $ do 
      ruleToHtml path
      -- ul ! A.id (stringValue "myUL") $ 
      --   li $
      --     H.span ! A.class_ (stringValue "caret") $ toHtml "Beverages"
      -- ul ! A.id (stringValue "myUL") $ 
      --   li $
      --     H.span ! A.class_ (stringValue "caret") $ toHtml "Beverages2"


ruleToHtml :: (?globals :: Globals) => RuleInfo -> Html 
ruleToHtml (AbsRule focusPhase goal gamma omega (x, assumption) expr ruleInfo delta) = do 
  ul ! A.id (stringValue "Rule") $ li $ do 
    H.span ! A.class_ (stringValue "caret") $ toHtml "Abs"
    ul ! A.id (stringValue "focusPhase") $ li $ toHtml (show focusPhase)
    ul ! A.id (stringValue "goal") $ li $ toHtml (pretty goal)
    ul ! A.id (stringValue "boundVar") $ li $ toHtml (pretty x)
    ul ! A.id (stringValue "expr") $ li $ toHtml (pretty expr)
  

ruleToHtml _ = do 
  ul ! A.id (stringValue "empty") $ li (toHtml "empty")



contextToHtml ::  Ctxt SAssumption -> Html 
contextToHtml = undefined 


printSynthOutput :: (?globals :: Globals) => Html -> IO ()
printSynthOutput html = do 
  writeFile (sourceFilePath -<.> "html") $ renderHtml html
  
