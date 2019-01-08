```
                                     ___             
                                    /\_ \            
   __   _  _    __      ___   __  __\//\ \      __   
 / _  \/\`'__\/ __ \  /' _ `\/\ \/\ \ \ \ \   /'__`\
/\ \_\ \ \ \//\ \_\ \_/\ \/\ \ \ \_\ \ \_\ \_/\  __/
\ \____ \ \_\\ \__/ \_\ \_\ \_\ \____/ /\____\ \____\
 \/___L\ \/_/ \/__/\/_/\/_/\/_/\/___/  \/____/\/____/
   /\____/                                           
   \_/__/
```

A functional programming language with a linear type system and fine-grained effects and coeffects via **graded modal types**.

A brief introduction to the Granule programming language can be found in [this extended abstract](http://www.cs.ox.ac.uk/conferences/fscd2017/preproceedings_unprotected/TLLA_Orchard.pdf) presented at TLLA'17. The type system is partly based on the one in ["Combining effects and coeffects via grading" (Gaboardi et al. 2016)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf).

## Example

Linearity means that the following is ill-typed:

```idris
dupBroken : forall (a : Type) . a -> (a, a)
dupBroken x = (x, x)
```

However, a graded modality can be employed to explain exactly how many times the
parameter here can be used:

```idris
dup : forall (a : Type) . a [2] -> (a, a)
dup [x] = (x, x)
```

Combining indexed types and bounded reuse in Granule leads to an interesting type
for the standard `map` function on sized lists ("vectors"):

```idris
--- Map function
map : forall (a : Type, b : Type, n : Nat)
    . (a -> b) [n] -> Vec n a -> Vec n b
map [_] Nil = Nil;
map [f] (Cons x xs) = Cons (f x) (map [f] xs)
```

This type explains that the parameter function `f` is used exactly `n` times, where `n` is the size
of the incoming list. Linearity ensures that the entire list is consumed exactly
once to the produce the result.

## Installation

The Granule interpreter requires Z3, for which installation instructions can be found [here](https://github.com/Z3Prover/z3). On mac, an easy way to install Z3 is via Homebrew:

    $ brew install z3

To install Granule, we recommend you use [Stack](https://docs.haskellstack.org/en/stable/README/):

    $ git clone https://github.com/granule-project/granule && cd granule && stack setup && stack install

If you have any problems building, this may be due to an outdated version of Stack; you can update Stack via `stack upgrade`.

## Executing Granule Programs

Granule program files have file extension `.gr`. Use the `gr` command to run the interpreter:

    $ gr examples/NonEmpty.gr
    Checking examples/NonEmpty.gr...
    Ok, evaluating...
    `main` returned:
    1

See the `examples` directory for more sample programs, or `frontend/tests/cases`
if you dare.

All contributions are welcome!
