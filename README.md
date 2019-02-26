```
                                     ___
                                    /\_ \
   __   _  _    __      ___   __  __\//\ \      __
 / _  \/\`'__\/ __ \  /' _ `\/\ \/\ \ \ \ \   /'__`\
/\ \_\ \ \ \//\ \_\ \_/\ \/\ \ \ \_\ \ \_\ \_/\  __/
\ \____ \ \_\\ \__/ \_\ \_\ \_\ \____/ /\____\ \____\
 \/___/\ \/_/ \/__/\/_/\/_/\/_/\/___/  \/____/\/____/
   /\____/
   \_/__/
```

Granule is a functional programming language with a linear type system and
fine-grained effects and coeffects via **graded modal types**.

A brief introduction to the Granule programming language can be found in the
[extended abstract presented at TLLA'17][1]. The type system is partly based on
the one in ["Combining effects and coeffects via grading" (Gaboardi et al.
2016)][2].

[1]: https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf
[2]: http://www.cs.ox.ac.uk/conferences/fscd2017/preproceedings_unprotected/TLLA_Orchard.pdf

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

This type explains that the parameter function `f` is used exactly `n` times,
where `n` is the size of the incoming list. Linearity ensures that the entire
list is consumed exactly once to the produce the result.

## Installation

Binary releases are currently available for MacOS only. If you need a newer
[release](https://github.com/granule-project/granule/releases) than is available
then please open an issue.

To build Granule from source, make sure you have
[Z3](https://github.com/Z3Prover/z3) and
[Stack](https://docs.haskellstack.org/en/stable/README/) on your system.

Now run

    git clone https://github.com/granule-project/granule \
    && cd granule \
    && stack setup \
    && stack install --test

More details about how to install can be found on the [wiki
page](https://github.com/granule-project/granule/wiki/Installing-Granule).

## Running the Interpreter

Granule program files have file extension `.gr`. Use the `gr` command to run the interpreter:

    $ gr examples/NonEmpty.gr
    Checking examples/NonEmpty.gr...
    OK, evaluating...
    1

See the `examples` directory for more sample programs, or `frontend/tests/cases`
if you dare.

### Setting the Path

Granule has a very basic import system. When `gr` encounters a line `import
A.B.C` anywhere in the file it will attempt to load the file located at
`$GRANULE_PATH/A/B/C.gr`, where `$GRANULE_PATH` defaults to `StdLib`, i.e. it
should work when you are running `gr` from within this project. For a more
stable setup which lets you run `gr` from any directory you can set the path
with the `--include-path` flag (see below).

### Configuration

Run `gr` with the `--help` flag for an overview of flags. Flags can be set

  1. in `~/.granule` (the same way as on the command line)
  2. on the command line
  3. at the top of the file (prepended with `-- gr `)

and have precedence in that order, e.g. flags set on the command line will
override flags in the config.

Example `.granule` file:

~~~sh
$ cat ~/.granule
--include-path /Users/alice/granule/StdLib
--solver-timeout 2000
~~~

### Accessibility

We aim to make Granule as inclusive as possible. If you experience any
accessibility hurdles, please open an issue.

#### Alternative Colours

The `--alternative-colors`/`--alternative-colours` flag will cause success
messages to be printed in blue instead of green, which may help with colour
blindness.

The `--no-color`/`--no-colour` flag will turn off colours altogether.

### Multi-Byte Unicode

The following symbols are interchangeable. You can destructively rewrite all
occurrences in your source file by passing
`--ascii-to-unicode`/`--unicode-to-ascii`. `--keep-backup` will save a backup of
the most recent copy of the input file with `.bak` appended.

| ASCII | Unicode |
|:---:|:---:|
| `forall` | `∀` |
| `Inf` | `∞` |
| `->` | `→` |
| `=>` | `⇒` |
| `<-` | `←` |
| `/\` | `∧` |
| `\/` | `∨` |
| `<=` | `≤` |
| `>=` | `≥` |
| `==` | `≡` |
| `\` | `λ` |

Usages of the operator `∘` get parsed as an application of `compose`.

### Literate Granule

Granule has some basic support for literate programs with Markdown and TeX.
By default code in `granule` code environments will be run. This can be
overridden with the flag `--literate-env-name`.

#### Markdown

The interpreter also takes markdown files with the extension `.md`, in which
case all fenced code blocks labelled with `granule` will get parsed as the input
source code. All other lines are ignored, but counted as whitespace to retain
line numbers for error messages.

~~~~ markdown
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
int c = 3;
~~~

```haskell
d :: Int
d = 4
```
~~~~

#### TeX

You can run Granule on the TeX file below with `gr --literate-env-name verbatim`.
You can use XeLaTeX to properly display multi-byte Unicode characters.

~~~ tex
\documentclass{article}

\title{Literate Granule (\TeX{}) Example}
\begin{document}
\author{Grampy Granule}
\maketitle

Writing things here.

\begin{verbatim}
import Prelude

foo : String
foo = "running code here"
\end{verbatim}
\end{document}
~~~


## Caveats

Granule is a research project to help us gain intuitions about using linearity
and graded modalities in programming. It is licensed under a permissive licence,
so you can use it for whatever, but please don't write your next spaceship
controller in Granule just yet. The interface is not stable (and nor is the
code). You have been warned...

~~~
            ( All contributions are welcome! )
      __//   /
    /.__.\
    \ \/ /
 '__/    \
  \-      )
   \_____/
_____|_|______________________________________
     " "
~~~