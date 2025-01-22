WIP notes

## Desired behaviour

Simple lifetimes, save on GC

- Local values are not heap allocated (safely!)
  - call stack? "locals stack" - locals need to survive across call frames
- Global values are heap allocated
- Global is default

In JSOCaml:

- a Global can be used in Local context (G < L)
- a Local cannot escape it's "region" (?? function body / scope / loop body / ref)
- a local parameter is a promise that the function will not escape the parameter
- a local return is a promise that the caller will not escape the return
- quirks?
  - utility to end regions early, "exclave"
  - tail positions special treatment, e.g. ret `drop local` not ok but ret `drop local ; ()` ok

## Notes

Need examples of what is and is not fine

Needs rules for safety

Will require annotating builtins especially mutable refs

Extension for promotions?

Locals need to live beyond their stack frame

Fine-grained lifetimes e.g. this local can live 0..2 call frames - nonsense?

In JS Locality is combined with Uniqueness/Affinity for borrows

Some behavioural similarity here with Private / Public - i.e. private does not escape to public context, public can be used in private

Should we drop Arb? Do we need it? Global as default. For formalisation do we need Unused as in Locality1?

ok:    (a : Global, b : Global) : Local
notok: (a : Local, b : Local) : Global

## Locality2

This is the implementation in frontend, expected behaviour in simple cases (see examples) - order is reverse of what I expect and not clear on route to formalisation - 0 is Local and 1 is Arb.

Local < Global < Arb

meet Local x = Local
meet x Local = Local
meet Global x = Global
meet x Global = Global
meet Arb Arb = Arb

join Arb x = Arb
join x Arb = Arb
join Global x = Global
join x Global = Global
join Local Local = Local

plus = join (?)
times = meet (?)

## Resources

[Oxidizing OCaml with Modal Memory Management](https://dl.acm.org/doi/pdf/10.1145/3674642) (JS)

[LocalGlobal.agda](https://github.com/granule-project/security-coeffects-mechanization/blob/4c0ae9ed41da2ede42e02f7baaa1cbfef78d9814/LocalGlobal.agda) (Locality1)

[OCaml with Jane Street extensions](https://github.com/janestreet/opam-repository/tree/with-extensions) (JSOCaml)
