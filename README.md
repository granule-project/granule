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

## Installation

The Granule interpreter requires Z3, for which installation instructions can be found [here](https://github.com/Z3Prover/z3). An easy way to install Z3 on mac is via Homebrew, e.g.,

    brew install z3

To install Granule, we recommend you use [Stack](https://docs.haskellstack.org/en/stable/README/):

    git clone https://github.com/dorchard/granule && cd granule && stack setup && stack install

## Executing Granule Programs

Granule program files have file extension `.gr`. Use the `gr` command to execute them (`-i` mutes info messages):

    $ gr -i examples/good/example.gr
    14

See the `examples` directory for more sample programs.

All contributions are welcome!
