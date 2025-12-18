{-# options_ghc -fno-warn-unused-imports #-}
{-# LANGUAGE NoOverloadedStrings #-}
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
import Language.Granule.Checker.Monad

import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Contexts
import Language.Granule.Synthesis.Common
import Language.Granule.Utils

import Control.Monad (forM_, zipWithM_)
import System.FilePath ((-<.>))



printSynthOutput :: (?globals :: Globals) => Html -> IO ()
printSynthOutput html = do 
  writeFile (sourceFilePath -<.> "html") $ renderHtml html

synthTreeToHtml :: (?globals :: Globals) => Expr () () -> RuleInfo -> Html 
synthTreeToHtml result path = 
  docTypeHtml $ do 
    H.head $ do 
      H.title  $ toHtml "Synthesis output"
      H.style  $ toHtml css
    -- 
    body $ do 
      H.p $ toHtml "The synthesised program is: "
      H.p ! A.style (stringValue "color: blue;") $ toHtml $ pretty result  
      H.p $ toHtml "Below is the synthesis search tree for this result. "
      H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ "Blue ")
      H.p ! A.style (stringValue "display: inline;") $ (toHtml $ "is used to indicate a synthesised term, ")
      H.p ! A.style (stringValue "color: green; display: inline;") $ (toHtml $ "green ")
      H.p ! A.style (stringValue "display: inline;") $ (toHtml $ "represnts assumptions, and ")
      H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ "red ")
      H.p ! A.style (stringValue "display: inline;") $ (toHtml $ "is used for goal types.")
      H.p $ toHtml "The tree can be expanded/collapsed by clicking nodes marked with an arrow."
      ul ! A.id (stringValue "outer") $ li $ do 
        successfulSynthPathToHtml path
      -- ul ! A.id (stringValue "outer") $ li $ do 
        -- fullSynthPathToHtml path
      
      H.script $ toHtml javaScript


successfulSynthPathToHtml :: (?globals :: Globals) => RuleInfo -> Html 
successfulSynthPathToHtml EmptyRuleInfo = error "stop"
successfulSynthPathToHtml (VarRule name assumption goal gamma omega delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml ("Var, using var:") 
      ; H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty name <> " : " <> pretty assumption)
      ; H.p ! A.style (stringValue "display: inline;") $ toHtml (" with goal: ")
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do
      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma
      li $ do 
        H.span ! A.class_ (stringValue (if null omega then "notCaret" else "caret")) $ toHtml (if null omega then "Ω = ∅" else "Ω")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml omega
      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta

successfulSynthPathToHtml (AbsRule focusPhase goal gamma omega (x, assumption) expr ruleInfo delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml "Abs, with goal:"
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma
      li $ do 
        H.span ! A.class_ (stringValue (if null omega then "notCaret" else "caret")) $ toHtml (if null omega then "Ω = ∅" else "Ω")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml omega

      li $ toHtml "Sub-term: "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: green; display: inline;") $ (toHtml $ pretty x <> " : " <> pretty assumption)
          ; H.p ! A.style (stringValue "display: inline;") $ (toHtml " bound in ")
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr)

        li $ successfulSynthPathToHtml ruleInfo
 
      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta

successfulSynthPathToHtml (AppRule focusPhase (x1, assumption1) goal gamma omega (x2, assumption2) expr1 ruleInfo1 delta1 expr2 ruleInfo2 delta2 delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml ("App, using var:") 
      ; H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x1 <> " : " <> pretty assumption1)
      ; H.p ! A.style (stringValue "display: inline;") $ toHtml (" with goal: ")
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma
      li $ do 
        H.span ! A.class_ (stringValue (if null omega then "notCaret" else "caret")) $ toHtml (if null omega then "Ω = ∅" else "Ω")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml omega

      -- Result sub-term
      li $ toHtml "Result-term: "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: green; display: inline;") $ (toHtml $ pretty x2 <> " : " <> pretty assumption2)
          ; H.p ! A.style (stringValue "display: inline;") $ (toHtml " bound in ")
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr1)
        li $ successfulSynthPathToHtml ruleInfo1

      -- Arg sub-term
      li $ toHtml "Arg-term: "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr2)
        li $ successfulSynthPathToHtml ruleInfo2

      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta


successfulSynthPathToHtml (BoxRule focusPhase goal gamma expr ruleInfo delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml "Box, with goal: "
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do 

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma

      li $ toHtml "Sub-term: "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr)

      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta

successfulSynthPathToHtml (UnboxRule focusPhase (x1, assumption1) goal gamma omega (x2, assumption2) expr ruleInfo delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml "Unbox, using var:"
      ; H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x1 <> " : " <> pretty assumption1)
      ; H.p ! A.style (stringValue "display: inline;") $ toHtml (" with goal: ")
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma
      li $ do 
        H.span ! A.class_ (stringValue (if null omega then "notCaret" else "caret")) $ toHtml (if null omega then "Ω = ∅" else "Ω")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml omega


      li $ toHtml "Sub-term: "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: green; display: inline;") $ (toHtml $ pretty x2 <> " : " <> pretty assumption2)
          ; H.p ! A.style (stringValue "display: inline;") $ (toHtml " bound in ")
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr)

        li $ successfulSynthPathToHtml ruleInfo

      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta



successfulSynthPathToHtml (ConstrRule focusPhase conId goal gamma expr ruleInfos delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml "Constr, using con: "
      ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty conId)
      ; H.p ! A.style (stringValue "display: inline;") $ (toHtml " with goal: ")
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do 

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma

      li $ toHtml "Sub-term(s): "
      ul $ do 
        li $ do 
          ; H.p ! A.style (stringValue "color: blue; display: inline;") $ (toHtml $ pretty expr)
        li $ forM_ ruleInfos successfulSynthPathToHtml

      li ! A.id (stringValue "context") $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta

successfulSynthPathToHtml (CaseRule focusPhase (x, assumption) goal gamma omega expr ruleInfos delta) = do 
    H.span ! A.class_ (stringValue "caret") $ do toHtml "Case, using var:"
      ; H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x <> " : " <> pretty assumption)
      ; H.p ! A.style (stringValue "display: inline;") $ toHtml (" with goal: ")
      ; H.p ! A.style (stringValue "color: red; display: inline;") $ (toHtml $ pretty goal)
    ul ! A.class_ (stringValue "nested") $ do

      li $ do 
        H.span ! A.class_ (stringValue (if null gamma then "notCaret" else "caret")) $ toHtml (if null gamma then "Γ = ∅" else "Γ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml gamma
      li $ do 
        H.span ! A.class_ (stringValue (if null omega then "notCaret" else "caret")) $ toHtml (if null omega then "Ω = ∅" else "Ω")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml omega

      li $ toHtml "Branches: "
      ul $ do 
        li $ forM_ ruleInfos (\(conId, boundVars, bExpr, bDelta, ruleInfo) -> 
          do 
            li ! A.id (stringValue "Branch") $ do 
              H.span ! A.class_ (stringValue "caret") $ toHtml (pretty conId)
              ul ! A.class_ (stringValue "nested") $ do 
                li $ zipWithM_ (\(x, assumption) index -> do
                  H.p ! A.style (stringValue "display: inline;") $ toHtml (if index == 0 then "" else ", ") 
                  H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x <> " : " <> pretty assumption)
                  H.p ! A.style (stringValue "display: inline;") $ toHtml (if index == ((length boundVars) - 1) then " bound in " else "")
                  H.p ! A.style (stringValue "color: blue; display: inline;") $ toHtml (if index == ((length boundVars) - 1) then pretty bExpr else "")
                  ) boundVars [0..]
                H.p ! A.style (stringValue "display: inline;") $ toHtml (if null boundVars then "No bindings in" else "")
                H.p ! A.style (stringValue "color: blue; display: inline;") $ toHtml $ (if null boundVars then pretty bExpr else "")
                li $ successfulSynthPathToHtml ruleInfo
          )
      li $ do 
        H.span ! A.class_ (stringValue (if null delta then "notCaret" else "caret")) $ toHtml (if null delta then "Δ = ∅" else "Δ")
        ul ! A.class_ (stringValue "nested") $ li $ do 
          contextToHtml delta


contextToHtml :: (?globals :: Globals) => Ctxt SAssumption -> Html 
contextToHtml [] = do 
  H.p ! A.style (stringValue "display: inline;") $ toHtml ""
contextToHtml [(x, assumption)] = do 
  H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x <> " : " <> pretty assumption)
contextToHtml ((x, assumption):rest) = do 
  H.p ! A.style (stringValue "color: green; display: inline;") $ toHtml (pretty x <> " : " <> pretty assumption)
  H.p ! A.style (stringValue "display: inline;") $ toHtml ", " 
  contextToHtml rest

  
javaScript :: String 
javaScript = "                                                                                \n\
            \ var toggler = document.getElementsByClassName(\"caret\");                       \n\
            \ var i;                                                                          \n\
            \                                                                                 \n\
            \ for (i = 0; i < toggler.length; i++) {                                          \n\
            \  toggler[i].addEventListener(\"click\", function() {                            \n\
            \    this.parentElement.querySelector(\".nested\").classList.toggle(\"active\");  \n\
            \    this.classList.toggle(\"caret-down\");                                       \n\
            \  });                                                                            \n\
            \ }                                                                               \n"

css :: String
css = "  body {                                                       \n\
        \    background-color: linen;                                 \n\
        \    font-family: \"Lucida Console\", monospace;              \n\
        \  }                                                          \n\
        \                                                             \n\ 
        \  h1 {                                                       \n\
        \    color: maroon;                                           \n\
        \    margin-left: 40px;                                       \n\
        \  }                                                          \n\
        \                                                             \n\
        \  ul, #outer {                                               \n\
        \    list-style-type: none;                                   \n\
        \  }                                                          \n\
        \                                                             \n\
        \  #outer {                                                   \n\
        \    margin: 0;                                               \n\
        \    padding: 0;                                              \n\
        \  }                                                          \n\
        \                                                             \n\
        \  .caret {                                                   \n\
        \    cursor: pointer;                                         \n\
        \    user-select: none;                                       \n\
        \  }                                                          \n\
        \                                                             \n\
        \  .caret::before {                                           \n\
        \    content: \"\\25B6\";                                     \n\
        \    color: black;                                            \n\
        \    display: inline-block;                                   \n\
        \    margin-right: 6px;                                       \n\
        \  }                                                          \n\
        \                                                             \n\
        \  .caret-down::before {                                      \n\
        \    transform: rotate(90deg);                                \n\
        \  }                                                          \n\
        \                                                             \n\
        \  .nested {                                                  \n\
        \    display: none;                                           \n\
        \  }                                                          \n\
        \                                                             \n\
        \  .active {                                                  \n\
        \    display: block;                                          \n\
        \  }  "                                                        

