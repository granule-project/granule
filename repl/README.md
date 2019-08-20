# `grepl` — Granule repl

A REPL for the Granule language

## Contents
- [Getting Started](#getting-started)
- [REPL Commands and Use](#repl-commands-and-use)
  - [help](#help-h)
  - [quit](#quit-q)
  - [load](#load-filepath-l)
  - [type](#type-term-t)
  - [show](#show-term-s)
  - [parse](#parse-expression-or-type-p)
  - [lexer](#lexer-string-x)
  - [debug](#debug-filepath-d)
  - [dump](#dump)
  - [module](#module-filepathm)
  - [reload](#reload-r)
- [Configuration File](#configuration-file)
  - [Config File Creation](#config-file-creation)
  - [Config File Format](#config-file-format)
  - [Config File Use](#config-file-use)

## Getting Started

To install `grepl`, run
```
$ stack install :grepl
```

To launch, run
```
$ grepl
```

## REPL Commands and Use

The following commands are available for use in the REPL
```
:help                (:h)
:quit                (:q)
:type <term>         (:t)
:type_scheme <type>  (:ts)
:show <term>         (:s)
:parse <expression>  (:p)
:lexer <string>      (:x)
:debug <filepath>    (:d)
:dump                ()
:load <filepath>     (:l)
:module <filepath>   (:m)
```


#### :help (:h)
<a id="help"></a>
Display the help menu

#### :quit (:q)
<a id="quit"></a>
Leave the REPL

#### :load <filepath\> (:l)
<a id="load"></a>
Load a file into the REPL.  This will erase content in state and replace with loaded file.
```
Granule> :l Vec.gr
Vec.gr, checked.
```
#### :type <term\> (:t)
<a id="type"></a>
Display the type of an expression in the REPL state
```
Granule> :l Vec.gr
Vec.gr, checked.

Granule> :t head
head :
  forall {a : Type, n : ↑Nat} .
   (Vec (n + 1) a) [0..1] -> a
```

#### :show <term\> (:s)
<a id="show"></a>
Show the Def for a given term in the REPL state
```
Granule> :m Nat.gr
StdLib\Nat.gr, checked.

Granule> :s add
Def ((32,1),(36,27)) (Id "add" "add") (Case ((34,3),(36,27)) (Val ((34,8),(34,8)) (Var (Id "n" "n_0"))) [(PConstr ((35,7),(35,7)) (Id "Z" "Z") [],Val ((35,17),(35,17)) (Var (Id "m" "m_1"))),(PConstr ((36,8),(36,8)) (Id "S" "S") [PVar ((36,10),(36,10)) (Id "n'" "n'_4")],App ((36,17),(36,27)) (Val ((36,17),(36,17)) (Constr (Id "S" "S") [])) (App ((36,20),(36,27)) (App ((36,20),(36,24)) (Val ((36,20),(36,20)) (Var (Id "add" "add"))) (Val ((36,24),(36,24)) (Var (Id "n'" "n'_4")))) (Val ((36,27),(36,27)) (Var (Id "m" "m_1")))))]) [PVar ((33,5),(33,5)) (Id "n" "n_0"),PVar ((33,7),(33,7)) (Id "m" "m_1")] (Forall ((32,7),(32,35)) [((Id "n" "n_2"),kConstr (Id "Nat=" "Nat=")),((Id "m" "m_3"),kConstr (Id "Nat=" "Nat="))] (FunTy (TyApp (TyCon (Id "N" "N")) (TyVar (Id "n" "n_2"))) (FunTy (TyApp (TyCon (Id "N" "N")) (TyVar (Id "m" "m_3"))) (TyApp (TyCon (Id "N" "N")) (TyInfix "+" (TyVar (Id "n" "n_2")) (TyVar (Id "m" "m_3")))))))
```
#### :parse <expression or type\> (:p)
<a id="parse"></a>
Run Granule parser on an expression and display Expr.  If input is not an expression parser will attempt to run it against the TypeScheme parser and display the TypeScheme
```
Granule> :p sum (Cons 1(Cons 2 Nil))
App ((1,1),(1,20)) (Val ((1,1),(1,1)) (Var (Id "sum" "sum"))) (App ((1,6),(1,20)) (App ((1,6),(1,11)) (Val ((1,6),(1,6)) (Constr (Id "Cons" "Cons") [])) (Val ((1,11),(1,11)) (NumInt 1))) (App ((1,13),(1,20)) (App ((1,13),(1,18)) (Val ((1,13),(1,13)) (Constr (Id "Cons" "Cons") [])) (Val ((1,18),(1,18)) (NumInt 2))) (Val ((1,20),(1,20)) (Constr (Id "Nil" "Nil") []))))
```
```
Granule> :p Int → Int
1:5: parse error
Input not an expression, checking for TypeScheme
Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int")))
```
#### :lexer <string\> (:x)
<a id="lexer"></a>
Run lexer on a string and display [Token]
```
Granule> :x sum (Cons 1(Cons 2 Nil))
[TokenSym (AlexPn 0 1 1) "sum",TokenLParen (AlexPn 4 1 5),TokenConstr (AlexPn 5 1 6) "Cons",TokenInt (AlexPn 10 1 11) 1,TokenLParen (AlexPn 11 1 12),TokenConstr (AlexPn 12 1 13) "Cons",TokenInt (AlexPn 17 1 18) 2,TokenConstr (AlexPn 19 1 20) "Nil",TokenRParen (AlexPn 22 1 23),TokenRParen (AlexPn 23 1 24)]
```
#### :debug <filepath\> (:d)
<a id="debug"></a>
Run the Granule debugger and display its output while loading a file
```
Granule> :d CombinatoryLogic.gr
<...Full AST will display here...>
<...Full pretty printed AST will display here...>
Debug: Patterns.ctxtFromTypedPatterns
Called with span: ((1,1),(2,7))
type: TyVar (Id "a" "a_1")

Debug: + Compare for equality
a_1 = a_1

Debug: Solver predicate


Debug: Patterns.ctxtFromTypedPatterns
Called with span: ((4,1),(6,16))
type: TyVar (Id "c" "c_5")
```
#### :dump
Display the contents of the REPL state in the form of `term : term type`
```
Granule> :l example.gr
example.gr, checked.

Granule> :dump
["dub : ((Int) |2|) → Int","main : Int","trip : ((Int) |3|) → Int","twice : forall c : Nat. ((((Int) |c|) → Int) |2|) → ((Int) |2 * c|) → Int"]
```

#### :module <filepath\>(:m)
<a id="module"></a>
Adds a file to the REPL by appending to the current REPL state
```
Granule> :m Prelude.gr
Prelude.gr, checked.
```
#### :reload (:r)
Reload the last file loaded into the Repl (included all the additionally loaded modules)
```
Granule> :l example.gr
example.gr, checked.
Granule> :r
example.gr, checked.
```
## Configuration File
<a id="configuration-file"></a>

The configuration file for `grepl` is the same as that as
`gr`. See README.md in the top-level directory for how to setup
the `.granule` file for the global configuration.