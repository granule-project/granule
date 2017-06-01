import qualified HappyParser
import Eval
import Expr
import Type
import Checker
import System.Environment

runEval :: String -> Bool -> IO ()
runEval input debug = do
  let ast = HappyParser.parseDefs input
  if debug
    then do
      putStrLn $ "AST:          " ++ (show ast)
      putStrLn $ "\nSource:\n"    ++ (pretty ast)
    else return ()
  putStrLn $ "\nEval (main):  " ++ (show $ eval ast)
  checked <- check ast debug
  putStrLn $ "\nType checker: " ++ (show' checked)


main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  runEval input (if length args >= 2 then args !! 1 == "-d" else False)

show' :: (Show a) => Either String a -> String
show' (Left s) = s
show' (Right x) = show x