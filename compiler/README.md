### Compiling Granule programs to Haskell

The compiler is provided as a binary named `grc`. 

To invoke the compilers, as well as pass the resulting Haskell code to GHC, use `stack exec` like this:

``` 
% stack build
% stack exec -- grc ./work-in-progress/deletearray.gr
Checking ./work-in-progress/deletearray.gr...
Ok, compiling...
Writing ./work-in-progress/deletearray.hs
% stack exec -- ghc ./work-in-progress/deletearray.hs
[1 of 1] Compiling Main             ( work-in-progress/deletearray.hs, work-in-progress/deletearray.o )
Linking work-in-progress/deletearray ...
% ./work-in-progress/deletearray

55.0
```

### Linking with Haskell libraries

As a convenience, there's a Haskell module included in this project called `Language.Granule.Runtime`. 
Anything exported from this module is available in generated Haskell code. Currently, it has some
top-level definitions implemented to match many of the primitives exposed in the compiler.
