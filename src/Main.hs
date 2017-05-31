import qualified HappyParser
import Eval
import Expr
import Type
import System.Environment

runEval :: String -> IO ()
runEval input = do
  let ast = HappyParser.parseDefs input
  putStrLn $ "AST:          " ++ (show ast)
  putStrLn $ "\nSource:\n"    ++ (pretty ast)
  putStrLn $ "\nEval (main):  " ++ (show $ eval ast)
  checked <- check ast
  putStrLn $ "\nType checker: " ++ (show' checked)


main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  runEval input

show' :: (Show a) => Either String a -> String
show' (Left s) = s
show' (Right x) = show x