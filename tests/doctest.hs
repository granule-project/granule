import Test.DocTest

main :: IO ()
main = do
  doctest ["src"]
  doctest ["app"]
