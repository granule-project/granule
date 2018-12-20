# Tips for Debugging Granule (Contribute!!)

The place to collect tips and tricks for debugging the Granule source. Please extend it!

# Lexer

Uses Alex. To run the lexer in GHCi (bear in mind that the actual path may change):

```
$ stack install; stack repl frontend/.stack-work/dist/x86_64-osx/Cabal-2.4.0.1/build/Language/Granule/Syntax/Lexer.hs
[...]
*Language.Granule.Syntax.Lexer> :t alexScanTokens
alexScanTokens :: String -> [Token]
```

# Parser

Uses Happy. To run the parser in GHCi (bear in mind that the actual path may change):

```
$ stack install; stack repl frontend/.stack-work/dist/x86_64-osx/Cabal-2.4.0.1/build/Language/Granule/Syntax/Parser.hs

[...]
*Language.Granule.Syntax.Parser> :set -XImplicitParams
*Language.Granule.Syntax.Parser> let ?globals = defaultGlobals in parseDefs "foo : Int\nfoo = 5"
AST [] [Def ((1,1),(2,7)) (Id "foo" "foo") (Val ((2,7),(2,7)) (NumInt 5)) [] (Forall ((0,0),(0,0)) [] (TyCon (Id "Int" "Int")))]
```

# Implicit parameters

For using functions that require implicit parameters within GHCi you can do something like this:

```
*Language.Granule.Syntax.Parser> :set -XImplicitParams
*Language.Granule.Syntax.Parser> let ?globals = defaultGlobals in parseDefs "foo : Int\nfoo = 5"
```

# Checker

```
$ stack repl source/Language/Granule/Checker/Checker.hs
*Language.Granule.Checker.Checker> :set -XImplicitParams
*Language.Granule.Checker.Checker>  let ?globals = defaultGlobals in runChecker initState $ checkDataCons $ DataDecl ((1,1),(1,23)) (Id "Choice" "Choice") [((Id "a" "a"),KType),((Id "b" "b"),KType)] Nothing [DataConstrA ((1,23),(1,23)) (Id "MkChoice" "MkChoice") [Box (CNat 1) (TyVar (Id "a" "a")),Box (CNat 1) (TyVar (Id "b" "b"))]]
```
