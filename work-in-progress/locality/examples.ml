let g2g : string @ global -> string @ global = fun x -> x

let g2l : string @ global -> string @ local = fun x -> x

let l2l : string @ local -> string @ local = fun x -> x

let a2l : string -> string @ local = fun x -> x

let a2g : string -> string @ global = fun x -> x

(* not ok
let l2g : 'a @ local -> 'a @ global = fun x -> x 
  *)

(* not ok
let l2a : string @ local -> string = fun x -> x 
  *)

let g2a : string @ global -> string = fun x -> x
