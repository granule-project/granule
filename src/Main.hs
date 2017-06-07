import qualified HappyParser
import Eval
import Expr
import Checker
import System.Environment

run :: String -> Bool -> IO ()
run input debug = do
  putStrLn "\n Gram v0.1.1.0"
  putStrLn "----------------------------------"
  let (ast, nameMap) = HappyParser.parseDefs input
  if debug
    then do
      putStrLn $ "AST:          " ++ (show ast)
      putStrLn $ "\nSource:\n"    ++ (pretty ast)
    else return ()
  putStrLn "\nType checking:    "
  checked <- check ast debug nameMap
  putStrLn $ showCheckerResult checked
  case checked of
    Right True -> do
      val <- eval ast
      putStr   $ "Evaluating main:\n\n"
      putStrLn $ show val
    _ -> return ()

main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  run input (if length args >= 2 then args !! 1 == "-d" else False)

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok."
showCheckerResult (Right False) = "Failed."