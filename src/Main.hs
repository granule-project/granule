import Eval
import Syntax.Expr
import Syntax.Parser
import Syntax.Pretty
import Checker.Checker
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  run input (if length args >= 2 then args !! 1 == "-d" else False)

run :: String -> Bool -> IO ()
run input debug = do
  putStrLn "\n Gram v0.1.2.0"
  putStrLn "----------------------------------"
  let (ast, nameMap) = parseDefs input
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

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok."
showCheckerResult (Right False) = "Failed."