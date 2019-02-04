

# Roadmap

This is an introduction to the linear functional programming language Granule,
based on our POPL'19 tutorial given in Cascais, Portugal @popl19granule.

The aim is to add linearity and graded modalities to our toolbox of
types-based reasoning principles, alongside household names like _parametric
polymorphism_ and _indexed types_. A solid background in a statically
typed language such as Haskell or ML is assumed, but if something doesn't make
sense, then please open an issue ....

We will look at successively more complex examples of linearity,
culminating in a verified implementation of the string manipulation function
`leftPad`.

The source of this document is a literate granule file (markdown), meaning that
all code in `granule` code blocks will get type checked and run when calling the
interpreter on this document.

## Linearity

Granule is based on the linear lambda calculus, which restricts our ability to
write programs due to its _substructural_ type system. We will explore this notion
rather casually here; if you want more details, I can recommend
[@cs152, chap. 17] or [@attapl, chap. 1]. The tl;dr is that Granule's type system
restricts _weakening_ (dropping variables) and _contraction_ (duplicating variables),
which our usual _structural_ type systems
 We retain
_exchange_  v

To get a feel for what
The following two functions, for example, violate linearity.
(Note that type variables are explicitly quantified.)


~~~ granule-bad
-- ✘
drop : forall a : Type . a → ()
drop x = ()

-- ✘
dup : forall a : Type . a → a × a
dup x = (x,x)
~~~



But we can type the following functions:

~~~ granule
id : forall a : Type . a → a
id x = x

flip : forall a : Type, b : Type . a × b → b × a
flip (x,y) = (y,x)
~~~


How can we write these functions? We use the postfix box modality `[]` to denote
unrestricted use of parameters. For example `a []` means that we use `a`
nonlinearly as much as we want—i.e. `a` is _cartesian_.

~~~ granule
drop' : forall a : Type . a [] → ()
drop' x = ()

dup' : forall a : Type . a [] → a × a
dup' x = (x, x)
~~~

Modalities in Granule are _graded_ by a _resource algebra_. One such algebra
tracks the exact usage of parameters via the usual natural number semiring:

~~~ granule
drop'' : forall a : Type . a [0] → ()
drop'' x = ()

dup'' : forall a : Type . a [2] → a × a
dup'' x = (x, x)
~~~

The resource algebra

In fact `[]` is just
sugar for `[0..∞]`, where `0..∞`


--
--
-- drop : forall a : Type . (List a) [0]  → ()
-- drop [_] = ()













drop1 : forall a : Type . (List a) [0] → ()
drop1 [_] = ()




--
--
--
--
--
-- --
-- --
-- --

-- polymorphism allows us to consume the list, but ignore the elements
drop2 : forall b : Type . List (b [0]) → ()
drop2 NilL           = ();
drop2 (ConsL [_] xs) = drop2 xs
-- --
-- --
-- -- __
-- --
-- --
-- --
-- --
-- --
-- -- -- define `map`
mapL : forall a : Type, b : Type . (a → b) [0..∞] → List a → List b
mapL [f] NilL = NilL;
mapL [f] (ConsL x xs) = ConsL (f x) (mapL [f] xs)
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
dub : Int [2] → Int
dub [x] = x + x

-- --
-- --
-- -- -- data Vector (n : Nat) a where
-- -- --   ConsV : a → Vector n a → Vector (n + 1) a;
-- -- --   NilV : Vector 0 a
-- --
import Vec
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- length' : forall a : Type, n : Nat
--         . Vec n a
--        → N n × Vec n a
-- length' Nil = (Z, Nil);
-- length' (Cons x xs) = let
--   (n, xs) = length' xs
--   in (S n, Cons x xs)
-- --
-- --
-- --
-- -- sq : Int [2] → Int
-- -- sq [x] = x*x
-- --
-- -- input : Vec 3 Int
-- -- input = Cons 1 (Cons 2 (Cons 3 Nil))
-- -- --
-- -- -- main : Vec 3 Int
-- -- -- main = let
-- -- --
-- -- --   map [sq] input
-- --
-- --
-- --
-- --
-- --
-- > Leftpad. Takes a padding character, a string, and a total length, returns
-- > the string padded to that length with that character. If length is less
-- > than the length of the string, does nothing. -- Credits: Hillel Wayne

-- leftPad 'a' 4 "bb"   = "aabb"
-- leftPad 'a' 4 "bbbb" = "bbbb"


leftPad : forall a : Type, m : Nat, n : Nat
        . a [n - m]
        → N n
        → Vec m a
        → Vec (m + (n - m)) a
leftPad [c] n str = let
  (m, str) = length' str
  in append (replicate (monus n m) [c]) str
-- --
-- --
-- -- -- id : (0 T : Type) → (a : T) → a
-- -- -- id _ x = x
-- --
-- -- -- main : Vec 3 Int
-- -- -- main = leftPad [0] (S (S Z)) input
-- --
-- --
-- --
-- --
-- -- --
-- -- --
-- -- --
data Patient = Patient
  (Int [Private]) -- Patient id
  (Int [Public])  -- Patient age

meanAge : List (Patient [0..1]) → Int [Public]
meanAge xs = meanAgeInner xs [0] [0]

meanAgeInner : List (Patient [0..1]) -- Patient database
       → Int [Public]
       → Int [Public]
       → Int [Public]
meanAgeInner (ConsL [Patient [id] [age]] NilL) [acc] [n]
    = [div (age + acc) (n + 1)];
meanAgeInner (ConsL [Patient [id] [age]] ps) [acc] [n]
    = meanAgeInner ps [age + acc] [n+1]

-- main : Int [Public]
-- main = meanAge (ConsL [Patient [1] [20]] (ConsL [Patient [2] [40]] NilL))
-- -- --

<!-- pandoc --output popl.html --filter pandoc-citeproc popl.gr.md -→

---
title: "Granule XXX"

author:
  name: Vilem-Benjamin Liepelt
  email: v.liepelt@kent.ac.uk

link-citations: true

references:
- id: popl19granule
  author:
  - family: Orchard
    given: Dominic
  - family: Eades
    given: Harley
  - family: Liepelt
    given: Vilem
  URL: https://popl19.sigplan.org/event/popl-2019-tutorialfest-t3-linear-and-graded-modal-types-for-fine-grained-program-reasoning
  title: "Linear and Graded Modal Types for Fine-Grained Program Reasoning"

- id: cs152
  author:
  - family: Chong
    given: Stephen
  issued:
  - year: 2016
  title: "Harvard CS152 (Programming Languages) Lecture Notes"
  chapter: 17 (Substructural Type Systems)
  URL: https://www.seas.harvard.edu/courses/cs152/2016sp/lectures/lec17-substructural.pdf

- id: attapl
  type: book
  author:
  - family: Pierce
    given: Benjamin C
  issued:
  - year: 2005
  title: Advanced topics in types and programming languages
  publisher: MIT press
...
