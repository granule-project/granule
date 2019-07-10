A taste of Granule
==================

This tutorial is based on Section 2 of the ICFP 2019 paper _Quantitative program
reasoning with graded modal types_ with additional complementary exercises.
Please refer to the paper for the technical details and a formalisation of the
overall system.

Are you ready?
--------------

This tutorial assumes some familiarity with ML/Haskell.

This Markdown document is a tutorial-style literate Granule program. Execute `gr
examples/intro.gr.md` on the command line to typecheck and run it (assuming that
you are in the granule source directory). Specify the function you want to run
with `--entry-point`.

The illtyped definitions are in a code environments called **grillN**
(**gr**anule **ill**typed where *N* is some number), which you can
give to the checker by passing the option `--literate-env grillN`. We
number ill-typed blocks here so that the reader can focus on
particular typing errors as we go through the tutorial.

Run `gr --help` to see various command line options.

For help with installing `gr`, the Granule interpreter, please see the
[installation instructions](https://github.com/granule-project/granule#installation).

See the [documentation](https://github.com/granule-project/granule#running-the-interpreter)
on how to use the interpreter.

Please do open an [issue](https://github.com/granule-project/granule/issues)
if something doesn't work as expected.


Combinators
-----------

Granule features a linear type system. This allows us to reason about
data in a resource-like manner. Linearity means that, by default, a
function must use each argument exactly once. What does "use" mean?
For concrete value constructors, we must **pattern match**. For
example, we can define the algebraic data type for booleans and give
the `not` function (which is linear) as:

~~~ granule
data Bool = False | True


not : Bool -> Bool
not False = True;
not True = False
~~~

Granule syntax is inspired by Haskell, but note the single colon for
typing rather than double, and note that the function arrow -> denotes
linear functions now.

For variables, linearity means we must either **return** them unchanged or
**pass them to a linear function**. If the variable is of a function type, then
**applying** that function is also a use. The following are two well-typed
examples, also showing polymorphism in Granule:

~~~ granule
id : forall {a : Type} . a -> a
id x = x


flip : forall {a b c : Type} . (a -> b -> c) -> b -> a -> c
flip f y x = f x y
~~~

Polymorphic type variables are explicit, given with their kind.  These
functions are both linear: they use their inputs exactly once.  The
`id` function binds its argument to some variable `x` on the left,
which it simply returns on the right. The `flip` function switches
around the order in which some function `f` takes arguments `y` and
`x` (lhs). The argument function `f` gets applied exactly once to `x`
and `y` (rhs), which are use exactly once by the parameter function as
indicated by their types.

<!-- This illustrates the design decision to retain the structural rule of
_exchange_, implicitly allowing arbitrary reordering of term variables. -->


Next, let us look at what happens when we write nonlinear functions.

~~~ grill1
drop : forall {a : Type} . a -> ()
drop x = ()
~~~
> Linearity error: Linear variable `x` is never used.

~~~ grill1
copy : forall {a : Type} . a -> (a, a)
copy x = (x,x)
~~~
> Linearity error: Linear variable `x` is used more than once.

(`gr examples/intro.gr.md --literate-env-name grill1`)

As you can see from the error messages following both definitions, Granule's
type checker does not accept these definitions.

Why would we want to enforce these restrictions?

By universally quantifying over the type of the inputs ("`forall {a : Type}`"),
we are claiming that we can implement these functions generically for any type;
however some resource-like data may be subject to specific usage protocols.
Examples:

  - prohibit cross-thread aliasing to prevent race conditions
  - close file handles exactly once and don't read from a closed handle
  - use a session-typed channel exactly once

If we want to reason about resources at the type level, we must renounce
*thoughtless* `drop`ping and `copy`ing. We will accommodate
non-linearity later using graded modalities.

For now, we briefly think about why linearity on its own can be
useful.

### Safer file handles

Granule provides an interface to files, which includes the following
operations, given here in a slightly simplified form that elides the
type indexing by handle capabilities for reading, writing and
appending, since this is orthogonal to our present narrative. The
exact types can be found
[here](https://github.com/granule-project/granule/blob/330682a280b8fb04305b9ad07f0b4b706afe99d1/frontend/src/Language/Granule/Checker/Primitives.hs#L176).

~~~ granule-interface
openHandle : IOMode -> String -> Handle <IO>

readChar : Handle -> (Handle, Char) <IO>

closeHandle : Handle -> () <IO>
~~~

The `openHandle` function
creates a handle, and its dual `closeHandle` destroys a handle. Linearity means
we can never *not* close a handle: we must use `closeHandle` to erase it. The
`readChar` function takes a readable handle and returns a pair of a readable
handle and a character. Logically, `readChar` can be thought of as consuming and
producing a handle, though at runtime this is backed by a single mutable data
structure. The `<IO>` type is a modality, written postfix, which captures I/O
side effects akin to Haskell's `IO` monad. We explain `<IO>` more later as it
approximates a more fine-grained graded modality. We now give two programs,
using Granule's notation for sequencing effectful computations akin to Haskell
`do` notation: of the form `let p_1 <- e_1; ...; p_n <- e_n in e`:


~~~ granule
firstChar : Char <IO>
firstChar = let
  h <- openHandle ReadMode "examples/intro.gr.md";
  (h, c) <- readChar h;
  () <- closeHandle h
  in pure c
~~~

(`gr examples/intro.gr.md --entry-point firstChar`)


~~~ grill2
forgetful : Char <IO>
forgetful = let
  h <- openHandle ReadMode "examples/intro.gr.md";
  (h, c) <- readChar h
  in pure c


outOfOrder : Char <IO>
outOfOrder = let
  h0 <- openHandle ReadMode "examples/intro.gr.md";
  () <- closeHandle h0;
  (h1, c) <- readChar h0
  in pure c
~~~

(`gr examples/intro.gr.md --literate-env-name grill2`)

The paper also provides the example reading two characters:

~~~ granule
twoChars : (Char, Char) <IO>
twoChars = let
  h <- openHandle ReadMode "examples/intro.gr.md";
  (h, c_1) <- readChar h;
  (h, c_2) <- readChar h;
  () <- closeHandle h
  in pure (c_1, c_2)
~~~

(`gr examples/intro.gr.md --entry-point twoChars`)

There is also the ill-typed example which contains both
the mistakes of `forgetful` and `outOfOrder` together:

~~~ grill3
bad : Char <IO>
bad = let
  h_1 <- openHandle ReadMode "somefile";
  h_2 <- openHandle ReadMode "another";
  () <- closeHandle h_1;
  (h_1, c) <- readChar h_1
  in pure c
~~~
(`gr examples/intro.gr.md --literate-env-name grill3`)

### Reintroducing Nonlinearity

The linear world is useful, but there are programs we want to write which are
fundamentally non-linear, such as `drop` and `copy`. Just like in Linear Logic,
Granule provides a type constructor for "requesting" nonlinearity. The typing
rules will enforce that the call site can actually provide this capability. This
type constructor is `[]`, written postfix.

~~~ granule
drop' : forall {a : Type}. a [] -> ()
drop' [x] = ()


copy' : forall {a : Type}. a [] -> (a, a)
copy' [x] = (x, x)
~~~

The “box” constructor `[]` can be thought of as the equivalent of
linear logic's `!` exponential for unrestricted use. Our choice of syntax alludes
to necessity modality ("box") from modal logic.

Since the parameters are now modal, of type `a []`, we can use an “unboxing”
pattern to bind a variable of `x` of type `a`, which can now be discarded or
copied freely in the bodies of the functions.

Note that a value of type `a []` is itself still subject to linearity: it must
be used:

~~~ grill4
dropNot : forall {a : Type}. a [] -> ()
dropNot xB = ()
~~~
> Linearity error: Linear variable `xB` is never used.

(`gr examples/intro.gr.md --literate-env-name grill4`)

Whilst this modality provides us with a non-linear binding for `x`, it however
gives a rather coarse-grained view: we cannot
distinguish the different forms of non-linearity employed by `copy'` and
`drop'`, which have the same type for their parameter.

### Going graded

To track fine-grained resource information, modalities in Granule are
*graded* by elements of a *resource algebra* whose
operations capture program structure.  One built-in resource algebra
counts variable use via the natural numbers semiring.  This enables
more precisely typed `copy` and `drop`:

~~~ granule
drop'' : forall {a : Type}. a [0] -> ()
drop'' [x] = ()


copy'' : forall {a : Type}. a [2] -> (a, a)
copy'' [x] = (x, x)
~~~

The function definitions replay
`drop'` and `copy'`, but the types now
provide exact specifications of the amount of non-linearity:
`0` and `2`.
We will see various other graded modalities in due course.

### Exercises

Solutions are at the end of this file.

#### 1.1
Make the following functions typecheck by addition of graded modalities at the
type level only where needed and the relevant unboxing pattern matches at the
value level. Give the most precise type.

~~~ grill
const : forall {a c : Type} . a -> (c -> a)
const x = \ctx -> x


ap : forall {a b c : Type}. (c -> a -> b) -> (c -> a) -> (c -> b)
ap f x = \ctx -> f ctx (x ctx)
~~~

#### 1.2

Consider the following definition:
~~~ granule
copyBool : Bool -> Bool × Bool
copyBool False = (False, False);
copyBool True  = (True, True)
~~~

Why does `copyBool` not violate linearity?

#### 1.3

Imagine you want to model a resource `Cake` which can be converted into
`Happiness` only via some linear function `eat`:

~~~ granule
data Cake = ACake
data Happiness = SomeHappiness

eat : Cake -> Happiness
eat ACake = SomeHappiness
~~~

How do we prevent greedy library clients from both `eat`ing and keeping their
`Cake`?

Section 2
---------

All the usual (Generalised) Algebraic Data Types from ML/Haskell work in Granule.
We saw a definition of `Bool` above; here we define `Maybe` (a.k.a. `option`):

~~~ granule
data Maybe a = None | Some a
~~~

<!-- Leave this for `grill`
~~~ grill5
data Maybe t = None | Some t
~~~
-->

To safely unwrap a `Maybe a` value to an `a`, we need to provide a default value
in case we actually hold a `None` in our hands.

~~~ grill5
fromMaybe : forall {a : Type} . a -> Maybe a -> a
fromMaybe d None     = d;
fromMaybe d (Some x) = x
~~~
> Linearity error: Linear variable `d` is never used.
(`gr examples/intro.gr.md --literate-env-name grill5`)

The equivalent of `fromMaybe` would be a valid Haskell or ML program, but Granule
rejects it and in fact this type is not inhabited in Granule. Since the `d`efault value
doesn't get used in the `None` case of the `Maybe a` parameter, we must wrap
it in a modality that witnesses/enables nonlinearity. However, we don't know
statically what it is supposed to be. For this Granule lets us declare a lower
and upper bound with an interval:

~~~ granule
fromMaybe : forall {a : Type} . a [0..1] -> Maybe a -> a
fromMaybe [d] None     = d;
fromMaybe [_] (Some x) = x
~~~

Intervals give us a fine-grained analysis, which is a feature that distinguishes
Granule from many other implementations of systems stemming from Linear Logic.


### Exercises

#### 2.1

At my first attempt of writing `fromMaybe`, I copy-pasted the first line and
replaced `None` with `Some x`, but I forgot to change the right hand side:

~~~ grill6
data Maybe t = None | Some t

fromMaybeNot : forall {a : Type} . a -> Maybe a -> a
fromMaybeNot d None     = d;
fromMaybeNot d (Some x) = d
~~~
(`gr examples/intro.gr.md --literate-env-name grill6`)

Granule rejects this definition with a type error. Most compilers can emit a
warning for unused bindings, which would help track down the bug in this case.
Write a piece of code that subtly fails its specification where such a warning
would not help. Check whether Granule would point out the issue.

#### 2.2

Consider the following program implementing logical ‘and’.

~~~ granule
and : Bool -> Bool [0..1] -> Bool
and False [_] = False;
and True  [q] = q
~~~

What is the technical term for the specific amount of nonlinearity denoted
by `[0..1]`?

Indexed Types
-------------


Indexed types give us type-level access to further information about
data. Granule supports user-defined indexed types, in a similar style
to Haskell's GADTs. We use the well-known
example of size-indexed lists (`Vec`) to write a partially [verified implementation
of `leftPad`](https://github.com/hwayne/lets-prove-leftpad#readme).

~~~ granule
data Vec (n : Nat) (a : Type) where
  Nil : Vec 0 a;
  Cons : a -> Vec n a -> Vec (n + 1) a


data N (n : Nat) where
  Z : N 0;
  S : N n -> N (n + 1)
~~~

Now we define some familiar list operations.

~~~ granule
append : forall {a : Type, m n : Nat} . Vec n a -> Vec m a -> Vec (n + m) a
append Nil ys = ys;
append (Cons x xs) ys = Cons x (append xs ys)
~~~

Notice that the type is exactly the same as in a nonlinear language.
Indexed types give us the useful property that the length of the output list is
indeed the sum of the length of the inputs. But in a linear language this type
guarantees even more: *every element from the inputs must appear in the
output.* In a nonlinear
setting, the implementation of this type could drop and copy
values, as long as the output has the correct length.

Polymorphism is important when reasoning about linearity: when we
can pattern match on the concrete values, then we consume them. In `append` we
cannot pattern match on the exact value of the elements of the list because of
their polymorphic type, hence the only thing we can do is to return it.

The most straightforward way to get the length of a list linearly is to
destruct the list until we reach the base case `Nil` and then reconstruct it as
we keep incrementing our `N`.

~~~ granule
length : forall {a : Type, n : Nat} . Vec n a -> (N n, Vec n a)
length Nil = (Z, Nil);
length (Cons x xs) =
  let (n, xs) = length xs in (S n, Cons x xs)
~~~



Next we define a function `rep` to produce a list of a desired length by
replicating a given element:

~~~ granule
rep : forall {a : Type, n : Nat} . N n -> a [n] -> Vec n a
rep Z [c]     = Nil;
rep (S n) [c] = Cons c (rep n [c])
~~~

Note that grades can depend on variables!

Now we define subtraction on our indexed naturals:

~~~ granule
sub : forall {m n : Nat} . {m >= n} => N m -> N n -> N (m - n)
sub m Z = m;
sub (S m') (S n') = sub m' n'
~~~

Granule lets us give preconditions in the context of type schemes (before `=>`).
These must hold where the function is used. Such predicates are discharged by
the external solver.

Finally, we can put the above functions together and define our left pad
function:

~~~ granule
leftPad : forall {t : Type, m n : Nat} . {m >= n} => N m -> Vec n t -> t [m - n] -> Vec m t
leftPad n str c = let (m, str) = length str in append (rep (sub n m) c) str
~~~


The type says that given a target length `m` and an input list with a
lesser or equal length `n`, we consume some padding element of type
`a` exactly `m - n` times to produce an output list of the target
length `m`. In Granule this type alone implies the correct implementation—modulo reorderings and nontermination—via:

- *Parametric polymorphism*: ensuring that the implementation cannot depend
on the concrete padding items provided or the items of the input list (hence we
use lists instead of strings);
- *Indexed types*: ensuring the correct size and explaining the exact
usage of the padding element;
- *Graded linearity*: ensuring that every item in the input list appears
exactly once in the output. The type `[m - n]` of the padding element
reveals its exact usage.


The type of `leftPad` in Granule is superficially similar to what we could
write in GHC Haskell or a fully dependently-typed language, except for the
nonlinearity of the padding element, a minor syntactic addition. However the
extra guarantees we get in a graded linear system like Granule's means we get
properties for free which we would otherwise have to prove ourselves.

### Exercises

#### 3.1

Consider the following type signature:

~~~ granule-interface
id_Vec : Vec n a -> Vec n a
~~~

A function of this type need not necessarily be the identity function on lists.
Why? Which structural rule could help us to reason about this?


Other graded modalities
-----------------------

In the file handles example we swept past the `<IO>` type
constructor.
This is an example of an effect-capturing
modality (the “diamond” constructor alludes to modal possibility), in the
spirit of Haskell's `IO` monad. However, Granule provides
*graded monads*, which can give a
more fine-grained account of effects.
`firstChar : Char <{Open, Read, IOExcept, Close}>`
which tells us its range of possible side effects via a set of labels, and notably
that there are no `Write` effects. Thus, Granule provides
graded modalities in two flavours: graded necessity/comonads for
coeffects (properties of input variables) and graded possibility/monads
for effects (properties of output computations).

A further graded modality that we have not seen yet provides
a notion of *information-flow security* via a lattice-indexed
graded necessity with labels `Public` and `Private`.
We can then, for example, define programs like the following which
capture the security level of values, and how levels are preserved
(or not) by functions:


~~~ granule
secret : Int [Private]
secret = [1234]
~~~

~~~ grill7
leak : Int [Public]
leak = hash secret
~~~
(`gr examples/intro.gr.md --literate-env-name grill7`)

~~~ granule
hash : forall {l : Level} . Int [l] -> Int [l]
hash [x] = [x*x*x]
~~~

~~~ granule
good : Int [Private]
good = hash secret
~~~

<!-- Leave for `grill`
~~~ grill7
secret : Int [Private]
secret = [1234]

hash : forall {l : Level} . Int [l] -> Int [l]
hash [x] = [x*x*x]
~~~
 -->

The End... For Now!
-------------------

There is another file, `further-examples.gr.md` if you are hungry for more.

Solutions
---------

#### 1.1

~~~ granule
const : forall {a c : Type} . a -> (c [0] -> a)
const x = \[ctx] -> x
~~~
Or equivalently:
~~~ granule
const' : forall {a c : Type} . a -> (c [0] -> a)
const' x [ctx] = x
~~~

~~~ granule
ap : forall {a b c : Type} . (c -> a -> b) -> (c -> a) -> (c [2] -> b)
ap f x = \[ctx] -> f ctx (x ctx)
~~~
Or equivalently:
~~~ granule
ap' : forall {a b c : Type} . (c -> a -> b) -> (c -> a) -> (c [2] -> b)
ap' f x [ctx] = f ctx (x ctx)
~~~

#### 1.2

> Why does `copyBool` not violate linearity?

Because in all cases we are pattern matching on concrete values on the left hand
side. On the right we are simply returning closed terms, which we are able to do
because the definition of `Bool` is in scope.


#### 1.3

> How do we prevent library clients from both `eat`ing and keeping their `Cake`?

We need to make `Cake` and `Happiness` abstract data types by hiding their
definitions and only export `eat`, as well as some restricted means of obtaining
a `Cake` in the first place. This prevents clients from implementing something like the following:

~~~ granule
copyCake : Cake -> Cake × Cake
copyCake ACake = (ACake, ACake)

eatAndKeep : Cake -> (Cake × Happiness)
eatAndKeep c = let (c1, c2) = copyCake c in (c1, eat c2)
~~~

Caveat: Granule doesn't yet have a means of selectively exporting definitions,
nor of enforcing linear usage of top-level definitions.

#### 2.1

One example:
~~~ grill8
--- Given two integers x and y, returns their sum and product resp.
foo : Int [2] -> Int [2] -> (Int, Int)
foo [x] [y] = (x + y, x * x)
~~~
> Grading error: `1` is not approximatable by `2` for type `Nat` because `Nat` denotes precise usage.
(`gr examples/intro.gr.md --literate-env-name grill8`)

Generally unused binding warnings will only trigger when a variable is not used
at all.

#### 2.2

> What is the technical term for the specific amount of nonlinearity denoted
by `[0..1]`?

_Affinity_, hence we say `and` is _affine_ in its second parameter. `[1..∞]`
denotes _relevance_. Intervals generalise this by allowing any lower and upper
bound for usage.

#### 3.1

> A function of this type need not necessarily be the identity function on lists.
Why?

Because the function could be reordering elements, e.g. reversing the list.

> Which structural rule could help us to reason about this?

_Exchange_, which controls the order in which term-level variables can be used.
