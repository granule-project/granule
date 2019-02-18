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
dupBroken : forall {a : Type} . a -> (a, a)
dupBroken x = (x, x)
```

However, a graded modality can be employed to explain exactly how many times the
parameter here can be used:

```idris
dup : forall {a : Type} . a [2] -> (a, a)
dup [x] = (x, x)
```

Combining indexed types and bounded reuse in Granule leads to an interesting type
for the standard `map` function on sized lists ("vectors"):

```idris
--- Map function
map : forall {a : Type, b : Type, n : Nat}
    . (a -> b) [n] -> Vec n a -> Vec n b
map [_] Nil = Nil;
map [f] (Cons x xs) = Cons (f x) (map [f] xs)
```

This type explains that the parameter function `f` is used exactly `n` times, where `n` is the size
of the incoming list. Linearity ensures that the entire list is consumed exactly
once to the produce the result.

## Installation

Make sure you have [Z3](https://github.com/Z3Prover/z3) and [Stack](https://docs.haskellstack.org/en/stable/README/) on your system.

Now run

    $ git clone https://github.com/granule-project/granule && cd granule && stack setup && stack install --test

More details about how to install can be found on the [wiki page](https://github.com/granule-project/granule/wiki/Installing-Granule).

## Running the Interpreter

Granule program files have file extension `.gr`. Use the `gr` command to run the interpreter:

    $ gr examples/NonEmpty.gr
    Checking examples/NonEmpty.gr...
    Ok, evaluating...
    `main` returned:
    1

See the `examples` directory for more sample programs, or `frontend/tests/cases`
if you dare.

### Literate Granule Files

The interpreter also takes markdown files with the extension `.md`, in which
case all fenced code blocks labelled with `granule` will get parsed as the input
source code. All other lines are ignored, but counted as whitespace to retain
line numbers for error messages.

    # Example literate granule (markdown) file

    Code blocks can be fenced with twiddles...

    ~~~ granule
    a : Int
    a = 1
    ~~~

    ... or backticks.

    ```granule
    b : Int
    b = 2
    ```

    The following code blocks will get ignored.

    ~~~
    c : Int
    c = 3
    ~~~

    ```not granule
    d : Int
    d = 4
    ```



### Options

`gr` takes several options, run `gr --help` for more information.

You can set default options in `$HOME/.granule`, e.g.:

```
$ cat ~/.granule
Options
  { debugging           = Nothing
  , noColors            = Just True
  , alternativeColors   = Nothing
  , noEval              = Nothing
  , suppressInfos       = Nothing
  , suppressErrors      = Nothing
  , timestamp           = Nothing
  , solverTimeoutMillis = Just 2000
  , includePath         = Just "Users/alice/granule/StdLib"
  , ascii2unicode       = Just True
  , keepBackupAscii     = Just False
  }
```

`Nothing` denotes that the default will be used and `Just x` means that the
default value gets overridden by `x`.

All contributions are welcome!
