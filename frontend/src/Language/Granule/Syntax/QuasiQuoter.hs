-- | Write Granule in your Haskell files!
--      [gr|
--      drop : a [] -> ()
--      drop _ = ()
--      |]

module Language.Granule.Syntax.QuasiQuoter
  ( module Language.Granule.Syntax.QuasiQuoter
  )
where

import Language.Granule.Syntax.Program
import Language.Granule.Syntax.Parser

import Language.Haskell.TH.Quote

gr :: QuasiQuoter
gr =
  QuasiQuoter
    { quoteExp =
        \str ->
            case parseModule "builtins" str of
              Right mod -> dataToExpQ (const Nothing) (moduleAST mod)
              Left err -> error err
    , quotePat  = undefined
    , quoteType = undefined
    , quoteDec  = undefined
    }
