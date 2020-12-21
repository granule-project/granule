# Rough guide to adding new graded necessity modalities (graded by pre-ordered semirings) to Granule

All source files in this guide are relative to
frontend/src/Language/Granule
unless otherwise stated.

For the sake of examples, I' assume here you are adding a new graded modality
whose semiring is called `Fruit`

## 1. Syntax

First decide what syntax you need for the grades. Grades can already
be numerical (natural numbers or floating point numbers) or type
constructors (capitalised names like Haskell) or omegas ∞ or
 intervals r..s or products r ,, s or sets.

If your new semiring can be encapsulated by some type constructors
(represented internally as `TyCon`)
then you do not need to add anything to the lexer
(Syntax/Lexer.x) or parser
(Syntax/Parser.y).

Grades are parsed into types, provided by the Syntax.Type `Type`
ADT. If you need to parse something new then you may need to augment
`Type` as well. Adding new data constructors there is fine. Do this
and re-compile and follow the errors. You will need to add a bunch of
boilerplate to do with unification, type quality, freshening, etc.
So it is better if you can get away with using type constructors
of numbers or sets!

Regardless of the above choices, you may want to add custom
pretty printing, so check out the `Syntax.Pretty` module for
this.

## 2. Primitives

You need to add a new primitive type for this "coeffect".
Built-in (primitive) type constructors are given in
Language.Granule.Primitives (Checker/Primitives.hs).
Add a line to `typeConstructors` for the type, e.g.,
`(mkId "Fruit", (kcoeffect, [], False))`
There is a section for this labelled `-- Coeffect types`.

If the members of your semiring are also type constructors
then also add these here, e.g.,
`(mkId "Apple", (tyCon "Fruit", [], False))`

If you have other operations you want to define on the
semiring, then you might want to add these here as type-level
operators, e.g., specifying their kind (Type) as `funTy (tyCon "Fruit") (tyCon "Fruit")`
and so on.

If have specialised computation level operations
using your grades then best thing to do is probably add
the in the Granule code inline here defined via
`builtinSrc` which uses the special keyword
`BUILTIN` on definitions. Basically treat this as a
place to give the type signatures. If you are using `BULTIN`,
you will need to give an interpretation for these primitives
in the evaluator `Interpreter.Eval` by extending the `builtIns`
list in there.


## 3. Equalities

The default approach for dealing with graded modalities is
compile everything to SMT. If you don't want to do that, you
will need to do work in Language.Granule.Types which defines
type equality mainly via the function `equalTypesRelatedCoeffectsInner`.

For a reference you might want to look down to the last case of
this function (roughly line 355) and see how type equality
drops down to speicalise functions for handling effect types
(monoid) (`effApproximates`) and session types (`sessionInequality`).

I'll assume now you want to use the SMT approach. In which case you
need to look at a Language.Granule.Constraints.

### 3.1. Compiling to SMT

The key functions you will need to modify are
`freshSolverVarScoped` and `compileCoeffect` and also
the symbolic representation used by Granule in

- A good starting point is to decide how you want to represent
your semiring in the SMT solver. You will need to modify
`Language.Granule.Checker.Constraints.SymbolicGrades`
(Checker/Constraints/SymbolicGrades.hs).
This modules defines `SGrade` which
is a unified symbolic representation for grades, and the gives various
functions over this like `symGradeTimes` which defines the semiring
multiplication and `symGradePlus` which defines the semiring addition
`symGradeEq` which defines equality. The ordering and units
are handled in Language.Granule.Checker.Constraints (more later).
Add an extra data constructor to `SGrade`. You might then define
some other data type (see `SNatX` as an example) or build your
representation our of some other symbolic feature already provided
by the SMT backend like `SInteger`, `SBool`.

- Once you've add the extra data constructor, you should add cases to some
   or all of the following:

    - `match` - tells SMT when the representations "match"
    - `natLike` (OPTIONAL) - if your underlying representation is supposed to be naturals
    - `symbolicMerge` - probably recursively defined onto the internal rep
    - `symGradeLess` (OPTIONAL) - if you want an additional < ordering (not the same
    as the pre-order
    - `symGradeEq` - eqaulity
    - `symGradeMeet` - (OPTIONAL) [partial] meet operation (may or may not cohere with preorder, up to you) This comes from a user using the meet operator (not the type checker itself)
    - `symGradeJoin` - similar to the above
    - `symGradePlus` - semiring addition
    - `symGradeTimes` - semiring multiplication

- Now you need to go into the `Constraints` module (Checker/Constraints.hs)
 and updated `freshSolverVarScoped` which works out how to compile a symbolic variable
 for all the different kinds of grade. This function is specialised
 on the type of grade (third argument), so you will most likely want to
 add a new case for your particular semiring type. e.g.,
 add a case matching `(TyCon (internalName -> "Fruit"))`. You
 can look at the others for the general pattern, but this is a CPS-style
 functiom, where the last argument is the continuation in which you
 are binding this fresh solver variable. For example:

      freshSolverVarScoped quant name (TyCon (internalName -> "Fruit")) q k =
          quant q name (\solverVar -> k (cond, SFruit solverVar))

 where `cond` is a symbolic SMT expression giving any constraints on the
 fresh variables (e.g., if there is some representational constraints involved).
 Otherwise the type of `solverVar` will get resolved to whatever you said
 the representation is. Look at the other cases for inspiration!

 Depending on your SMT representation you may need to add an instance
 of `QuantifiableScoped`. But if you are just using integers, bools, floats,
 or combinations of other `SymGrade`s, then you won't need to.

- You will probably need to add several cases to the `compileCoeffect`
function which explains how to translate/compile the type representation of
grades into `SGrade`s:

     - Compile your semiring elements. This will of course depend on how you
      represented your semiring in `Type`. I'll assume that you managed to do it
      with `TyCon` (constructors), so now we should add cases for these.
      Note the first parameter is the grade term, the second is the type of it,
      so you probably want to match on the second paramter first, e.g.

           compileCoeffect grade (TyCon (internalName -> "Sec")) _ = do
               .....

              return (SSec rep, cond)

     where `rep` is your SMT representation and `cond` is any other conditions
     that come with this (might just be `sTrue`, i.e., no further constraints).

    - Find the case of `compileCoeffect` dealing with `TyGrade k' 0` - this is
    where you need to say how `0` (semiring additive unit) is compiled. This is a big `case` matching on
    the coeffect type `k`. You can probably just add a case to the part matching
    on a `TyCon` internal name.

    - Find the case of `compileCoeffect` dealing with `TyGrade k' 1` - this is
    where you need to saw how `1` (semiring multiplicative unit) is compiled.
    Similar approach as for 0.

    - Lastly add a case to `approximatedByOrEqualConstraint` which defines the
    semiring predorder where `approimatedByOrEqualConstraint r s` means that `r <= s`
    according to our theory, e.g., that `s` overapproximates `r`. For example,
    if we were doing BLL then this would be the normal natural number ordering
    since `1` use is less than `2` uses.
