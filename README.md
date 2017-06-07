# Gram
A statically typed functional language with graded modal types, including for coeffects and effects.
The type system is based on the one in ["Combining effects and coeffects via grading" (Gaboardi et al. 2016)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf)

## Installation

To install using Stack:

    git clone https://github.com/dorchard/gram-language
    cd gram-language
    stack install

To install using only Cabal:

    git clone https://github.com/dorchard/gram-language
    cd gram-language
    cabal install

## Executing Gram Programs

Gram program files have file extension `.gr`—use the `gram` command to execute them:

    $ gram examples/ex1.gr

     Gram v0.1.1.0
    ----------------------------------

    Type checking:    Ok.
    Evaluating main:

    15

See the `examples` directory for more sample programs.

All contributions are welcome!
