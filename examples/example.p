dub : [Int] 2 -> Int
dub = \x -> let [y : Int] = x in y + y

trip : [Int] 3 -> Int
trip = \x -> let [y : Int] = x in y + y + y

twice : [[Int] c -> Int] 2 -> [Int] (c + c) -> Int
twice = \gBox -> \xBox -> 
            let [g : [Int] 2 -> Int] = gBox in
            let [x : Int]            = xBox in
            g [x] + g [x]

main : Int
main = twice [dub] [1] + twice [trip] [1]
