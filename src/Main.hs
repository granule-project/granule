------------------
------ Gram ------
------------------

import Eval
import Syntax.Parser
import Syntax.Pretty
import Checker.Checker
import System.Environment

version = "Gram v0.1.3.0"

main :: IO ()
main = do
  args <- getArgs
  -- Get the filename
  input <- readFile (head args)
  -- Flag '-d' turns on debug mode
  run input (if length args >= 2 then args !! 1 == "-d" else False)

run :: String -> Bool -> IO ()
run input debug = do
  -- Welcome message
  putStrLn $ "\n" ++ version

  -- Parse
  let (ast, nameMap) = parseDefs input

  -- Debugging mode produces the AST and the pretty printer
  if debug
    then do
      putStrLn $ "AST:          " ++ (show ast)
      putStrLn $ "\nSource:\n"    ++ (pretty ast)
    else return ()

  -- Type check
  checked <- check ast debug nameMap
  putStrLn $ showCheckerResult checked

  case checked of
    -- If type checking succeeds then evaluate the program...
    Right True -> do
      val <- eval ast
      putStrLn $ pretty val
    _ -> return ()

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok."
showCheckerResult (Right False) = "Failed."