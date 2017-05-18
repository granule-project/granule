main : Int
main =
  let add = \x -> \y -> x + y in 
  let add5 = add 5 in
  add5 3
