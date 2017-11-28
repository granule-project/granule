module Checker.LaTeX where

import Data.List (intercalate)
import Data.Monoid

data Derivation =
  Node String [Derivation] | Leaf String

instance Show Derivation where
  show (Leaf s) = s
  show (Node c premises) =
    "\\dfrac{" <> intercalate " \\quad " (map show premises) <> "}{" <> c <> "}"

mkDocument doc =
 "\\documentclass{article}\
 \\\usepackage{amsmath}\
 \\\newcommand{check}[4]{#1 \\vdash #2 \\Leftarrow #3}\
 \\\begin{document}" <> doc <>
 "\\end{document}"