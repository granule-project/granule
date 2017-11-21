------------------
------ Granule ------
------------------

import Eval
import Syntax.Parser
import Syntax.Pretty
import Checker.Checker
import System.Environment

version :: String
version = "Granule v0.3.5.0"

main :: IO ()
main = do
  args <- getArgs
  case args of
    []      -> putStrLn "Usage: gr <SOURCE_FILE>"
    (src:_)  -> do
      -- Get the filename
      input <- readFile src
      -- Flag '-d' turns on debug mode
      run input (Debug $ if length args > 1 then args !! 1 == "-d" else False)

newtype Debug = Debug Bool


{-| Run the input through the type checker and evaluate.
>>> run "main : Int\nmain = (\\x -> \\y -> x * y) 3 5\n" (Debug False)
Granule ...
Ok.
15
-}
run :: String -> Debug -> IO ()
run input (Debug debug) = do
  -- Welcome message
  putStrLn version

  -- Parse
  (ast, nameMap) <- parseDefs input

  -- Debugging mode produces the AST and the pretty printer
  if debug
    then do
      putStrLn $ "AST:\n" ++ show ast
      putStrLn $ "\nSource:\n"    ++ pretty ast
    else return ()

  -- Type check
  checked <- check ast debug nameMap
  putStrLn $ showCheckerResult checked

  case checked of
    -- If type checking succeeds then evaluate the program...
    Right True -> do
      val <- eval debug ast
      case val of
        Just val' -> putStrLn $ pretty val'
        Nothing   -> return ()
    _ -> return ()

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok."
showCheckerResult (Right False) = "Failed."
