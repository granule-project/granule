------------------
------ Granule ------
------------------

import Eval
import Syntax.Parser
import Syntax.Pretty
import Checker.Checker

import Data.List (intercalate)
import System.Environment
import System.Exit (die)

version :: String
version = "Granule v0.3.9.0"

main :: IO ()
main = do
  args <- getArgs
  case args of
    []      -> putStrLn $ version ++ "\nUsage: gr <SOURCE_FILE> [-d]"
    (src:flags)  -> do
      -- Get the filename
      input <- readFile src
      -- Flag '-d' turns on debug mode
      run input (Debug $ "-d" `elem` flags)

newtype Debug = Debug Bool


{-| Run the input through the type checker and evaluate.
>>> run "main : Int\nmain = (\\x -> \\y -> x * y) 3 5\n" (Debug False)
ok
15
-}
run :: String -> Debug -> IO ()
run input (Debug debug) = do
  -- Parse
  (ast, nameMap) <- parseDefs input

  -- Debugging mode produces the AST and the pretty printer
  if debug
    then do
      putStrLn $ "AST:\n" ++ show ast
      putStrLn $ "\nSource:\n" ++ (intercalate "\n" $ map pretty ast)
      putStrLn $ "\nName map:\n" ++ show nameMap
    else return ()

  -- Type check
  checked <- check ast debug nameMap
  showCheckerResult checked

  case checked of
    -- If type checking succeeds then evaluate the program...
    Right True -> do
      val <- eval debug ast
      case val of
        Just val' -> putStrLn $ pretty val'
        Nothing   -> return ()
    _ -> return ()

showCheckerResult :: Either String Bool -> IO ()
showCheckerResult (Left s) = die s
showCheckerResult (Right True) = putStrLn "ok"
showCheckerResult (Right False) = die "failed"
