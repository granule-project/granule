# Granule
A statically typed functional language with graded modal types, including fine-grained coeffect and effect types.
A brief introduction can be found in [this extended abstract](http://www.cs.ox.ac.uk/conferences/fscd2017/preproceedings_unprotected/TLLA_Orchard.pdf) presented at TLLA'17.

The type system is partly based on the one in ["Combining effects and coeffects via grading" (Gaboardi et al. 2016)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf).

## Installation

Granule requires Z3, for which installation instructions can be found [here](https://github.com/Z3Prover/z3). An easy way to install Z3 on mac is via Homebrew, e.g.,

    brew install z3

To install Granule, we recommend you use [Stack](https://docs.haskellstack.org/en/stable/README/):

    git clone https://github.com/dorchard/granule && cd granule && stack setup && stack install

## Executing Granule Programs

Granule program files have file extension `.gr`. Use the `gr` command to execute them:

    $ gr examples/example.gr
    Granule v0.2.1.0
    Ok.
    14

See the `examples` directory for more sample programs.

All contributions are welcome!
