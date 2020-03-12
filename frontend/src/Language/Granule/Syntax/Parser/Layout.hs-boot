module Language.Granule.Syntax.Parser.Layout where

import Language.Granule.Syntax.Parser.Alex
import Language.Granule.Syntax.Parser.Tokens

offsideRule      :: LexAction Token
newLayoutContext :: LexAction Token
emptyLayout      :: LexAction Token