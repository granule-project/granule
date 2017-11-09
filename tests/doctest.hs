import Test.DocTest

main :: IO ()
main = do
  doctest ["app"]
  doctest ["src"]
