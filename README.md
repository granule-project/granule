# Gram
A statically typed functional language with graded modal types, including fine-grained coeffect and effect types.
The type system is partly based on the one in ["Combining effects and coeffects via grading" (Gaboardi et al. 2016)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf).

## Installation

Gram requires Z3, for which installation instructions can be found [here](https://github.com/Z3Prover/z3). An easy way to install Z3 on mac is via Homebrew, e.g.,

    brew install z3
    
To install Gram using Stack:

    git clone https://github.com/dorchard/gram-language
    cd gram-language
    stack install

To install Gram using only Cabal:

    git clone https://github.com/dorchard/gram-language
    cd gram-language
    cabal configure
    cabal install

## Executing Gram Programs

Gram program files have file extension `.gr`—use the `gram` command to execute them:

    $ gram examples/ex1.gr

     Gram v0.1.2.0
    ----------------------------------

    Type checking:    Ok.
    Evaluating main:

    15

See the `examples` directory for more sample programs.

All contributions are welcome!
