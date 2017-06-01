idLike : [Int] 1 -> Int
idLike = \x -> let [y : Int] = x in y

test : Int -> [Int] 2 -> Int
test = \z -> \x -> let [y : Int] = x in y + y + (idLike [z])

threePlus : [Int] 3 -> Int
threePlus = \z -> let [x : Int] = z in x + x + x

twice : [[Int] 2 -> Int] 2 -> [Int] 4 -> Int
twice = \f -> \x -> let [g : [Int] 2 -> Int] = f in
                   let [z : Int]             = x
                   in g [z] + g [z]

dub : [[Int] c -> Int] 2 -> [Int] (2 * c) -> Int
dub = \f -> \x -> let [g : [Int] c -> Int] = f in
                  let [z : Int] = x
                  in g [z] + g [z]


main : Int
main = dub [(test 1)] [2] + dub [threePlus] [1]
