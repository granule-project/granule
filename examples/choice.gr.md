# Polymorphism and Nonlinearity

This literate granule file gives an example of how parametric polymorphism
allows us to mix different levels of nonlinearity.

~~~ granule

import Choice
import Prelude

~~~

The `Choice` api for reference:

    choice : a [0..1] -> b [0..1] -> Choice a b
    choose1 : Choice a b -> a
    choose2 : Choice a b -> b

~~~ granule

--- Square a number, but only if the guard is true
squareOrIdentity : Bool -> Int [1..2] -> Int
squareOrIdentity g [n] = if g then n * n else n


example : Int
example =
  let [myChoice] : (Choice (Int [1..2]) Bool) [2]
    = [choice [[2]] [True]] in
  let b = choose2 myChoice in
  let i = choose1 myChoice in
  squareOrIdentity b i

~~~

Actually, the type annotation in the `let` isn't even needed:

~~~ granule

main : Int
main =
  let [myChoice] = [choice [[2]] [True]] in -- the grade `[2]` gets inferred
  let b = choose2 myChoice in
  let i = choose1 myChoice in
  squareOrIdentity b i

~~~
