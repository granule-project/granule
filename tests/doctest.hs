import Test.DocTest

main :: IO ()
main = do
  doctest ["source"]
  doctest ["command-line-interface"]
