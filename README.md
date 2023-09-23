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

An introduction to Granule can be found in our paper [Quantitative
program reasoning with graded modal types][1]. More details of the project
can be found on the [project website][2].

[1]: https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
[2]: https://granule-project.github.io/

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
    && stack install

This will instance the main frontend `gr` and the interactive mode
`grepl`.

More details about how to install can be found on the [wiki
page](https://github.com/granule-project/granule/wiki/Installing-Granule).

## Documentation

[Granule standard library documentation](https://granule-project.github.io/docs/)

You can run Granule in a mode that generates documentation in
the `docs` directory of the compiler top-level with the command:

     gr --grdoc filename

You can generate all the docs for the standard library by running

     gr --grdoc StdLib/*.gr
     gr --grdoc StdLib/*.gr

(Note the second run here, which stabilises the hyperlinks between modules for multi-file runs).

## Compiler

### Granule -> Haskell compiler

This provided by `grc` which takes a .gr file as input and outputs a .hs file of the code compiled to Haskell which imports the [Language.Granule.Runtime](https://github.com/granule-project/granule/blob/main/runtime/src/Language/Granule/Runtime.hs) module (so you need this in the path if you want to then compiler the resulting .hs file).

### LLVM compiler

If you would also like to install the LLVM compiler (experimental and a
work in progress) you can get this from its [separate repo](https://github.com/granule-project/granule-compiler-llvm) and install it via:

    stack install :grc


## Running the Checker + Interpreter

Granule program files have file extension `.gr`. Use the `gr` command to run the interpreter:

    $ gr examples/NonEmpty.gr
    Checking examples/NonEmpty.gr...
    OK, evaluating...
    1

A good starting point for learning about Granule is the tutorial given in
[examples/intro.gr.md](https://github.com/granule-project/granule/blob/master/examples/intro.gr.md).

On Windows, you may have issues with unicode, for which there is a work around by
setting the code page to UTF-8 (via `chcp.com 65001` https://stackoverflow.com/questions/25373116/how-can-i-set-my-ghci-prompt-to-a-lambda-character-on-windows). You may also want to run without colours
`gr --no-color`.

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

### Command line completion

See [here](https://github.com/pcapriotti/optparse-applicative#bash-zsh-and-fish-completions)
for how to install completion scripts for your shell, although we recommend
dynamically loading the completions in your shell's startup script to account
for changes in `gr`'s interface; e.g. for `fish` on MacOS:

~~~ fish
echo "#granule
gr --fish-completion-script (which gr) | source" >> ~/.config/fish/config.fish
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
| `exists` | `∃` |
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
