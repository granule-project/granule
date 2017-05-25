import qualified HappyParser
import Eval
import Expr
import Type
import System.Environment

runEval :: String -> IO ()
runEval input = do
  let ast = HappyParser.parseDefs input
  putStrLn $ "AST:          " ++ (show ast)
  putStrLn $ "Source:       " ++ (pretty ast)
  putStrLn $ "Eval (main):  " ++ (show $ eval ast)
  checked <- check ast
  putStrLn $ "Type checker: " ++ (show' checked)
--  putStrLn $ "Type: " ++

main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  runEval input

show' :: (Show a) => Either String a -> String
show' (Left s) = s
show' (Right x) = show x