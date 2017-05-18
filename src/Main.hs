import qualified HappyParser
import Eval
import Expr
import System.Environment

runEval :: String -> IO ()
runEval input = do
  let ast = HappyParser.parseDefs input
  putStrLn $ "AST: " ++ (show ast)
  putStrLn $ "Source: " ++ (pretty ast)
  putStrLn $ "Eval (main): " ++ (show (eval ast))
--  putStrLn $ "Type: " ++

main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  runEval input
