# Example expression

main : Int
main = ((\f -> \x -> f (x + 1)) (\x -> x)) 4
