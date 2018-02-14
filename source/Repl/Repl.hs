{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Repl.Repl where

-- import Control.Exception (SomeException, try)
import Control.Monad.State
import System.Console.Haskeline
-- import System.Console.Haskeline.MonadException
import System.Exit

import Utils 
import Repl.Queue
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Repl.ReplParser
import Checker.Checker

type Qelm = (Id, Def)
type REPLStateIO = StateT (Queue (QDefName, QDefDef)) IO

instance MonadException m => MonadException (StateT (Queue (QDefName, QDefDef)) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'                       

data QDefName = RVar Id  | DefName Id
    deriving (Show, Eq)
data QDefDef  = DefTerm Def
    deriving Show


getQDefM :: (QDefName, QDefDef) -> REPLStateIO (Id, Def)
getQDefM e@(RVar x, DefTerm t) = return (x , t)
getQDefM e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "

getQDef :: (QDefName, QDefDef) -> (Id, Def)
getQDef e@(RVar x, DefTerm t) = (x , t)
getQDef e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "

-- Extract only closed terms from queue
getQCTM :: Queue (QDefName,QDefDef) -> Queue Qelm -> REPLStateIO (Queue Qelm)
getQCTM (Queue [] []) qCV = return $ qCV
getQCTM q qCV = getQDefM (headQ q) >>= (\x -> case x of 
                 cv -> getQCTM (tailQ q) (enqueue cv qCV))
                 

-- Extract only closed terms from queue, non-monadic version
getQCT :: Queue (QDefName,QDefDef) -> Queue Qelm -> (Queue Qelm)
getQCT (Queue [] []) qCV = qCV
getQCT q qCV = case getQDef (headQ q) of 
                 cv -> getQCT (tailQ q) (enqueue cv qCV)
                 
                
io :: IO a -> REPLStateIO a
io i = liftIO i

prettyDef :: (QDefName, QDefDef) -> String
prettyDef elem = let t = getQDef elem in "let "++" = "++(pretty t)
    
pop :: REPLStateIO (QDefName, QDefDef)
pop = get >>= return.headQ

push :: (QDefName, QDefDef) -> REPLStateIO ()
push t = do
  q <- get
  put (q `snoc` t)

-- **** 
-- unfoldQueue :: (Queue Qelm) -> (Queue Qelm)
-- unfoldQueue q = fixQ q emptyQ step
 -- where
   -- step :: (Def, Def) -> t -> Queue Qelm -> Queue Qelm
   -- step e@(x,t) _ r = (mapQ (substDef t x) r) `snoc` e
    -- where
      -- substDef :: Def -> Def -> Qelm -> Qelm
      -- substDef x t (y, t') = (y, subst x t t')  
      
-- unfoldDefsInTerm :: (Queue Qelm) -> Expr -> Expr
-- unfoldDefsInTerm q t =
   -- let uq = toListQ $ unfoldQueue q
    -- in subst uq t

containsTerm_Qelm :: Queue Qelm -> QDefName -> Bool
containsTerm_Qelm (Queue f r) v@(RVar vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))
containsTerm_Qelm (Queue f r) v@(DefName vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))
      
containsTerm :: Queue (QDefName,QDefDef) -> QDefName -> Bool
containsTerm (Queue [] []) _ = False
containsTerm q v = (containsTerm_Qelm (getQCT q emptyQ) v) 

-- processFiles :: [FilePath] -> (FilePath -> IO a) -> (FilePath -> IO a) -> IO [[a]]
-- processFiles globPatterns e f = forM globPatterns $ (\p -> do
    -- filePaths <- glob p
    -- case filePaths of 
        -- [] -> (e p) >>= (return.(:[]))
        -- _ -> forM filePaths f)

readToQueue :: (?globals::Globals) => FilePath -> IO ExitCode
readToQueue pth = do
    pf <- parseDefs =<< readFile pth
    case pf of
        (ast, maxFreshId) -> do
            let ?globals = ?globals { freshIdCounter = maxFreshId }
            checked <- check ast
            case checked of
                Ok -> do
                    forM ast $ \idef ->  return $ loadInQueue idef
                    return ExitSuccess
                    
readToQueue' :: (?globals::Globals) => FilePath -> REPLStateIO()
readToQueue' pth = do
    pf <- return $ parseDefs =<< readFile pth
    case pf of
        (ast, maxFreshId) -> do
            let ?globals = ?globals { freshIdCounter = maxFreshId }
            checked <- return $ check ast
            case checked of
                Ok -> loadInQueue' ast

loadInQueue' :: [Def] -> REPLStateIO ()
loadInQueue' [] = return ()
loadInQueue' (x:xs) = do
    loadInQueue x
    loadInQueue' xs

  
loadInQueue :: Def -> REPLStateIO ()       
loadInQueue def = let def'@(Def _ id _ _ _) = def in -- Def s id ex [p] ts
                    push (RVar id, DefTerm def')  

-- noFileAtPath :: FilePath -> IO ExitCode
-- noFileAtPath pt = do
    -- print $ "The file path "++pt++" does not exist"
    -- return (ExitFailure 1)
                   



                    
handleCMD :: String -> REPLStateIO ()
handleCMD "" = return ()
handleCMD s =    
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> io $ putStrLn msg
  where      
    handleLine DumpState = get >>= io.print.(mapQ prettyDef)
    
    -- handleLine (LoadFile ptr) = processFiles ptr noFileAtPath readToQueue
        
        
                
        

   
-- getFV :: Expr -> [Id Expr]
-- getFV t = fv t :: [Id Expr]

helpMenu :: String                          
helpMenu = 
      "-----------------------------------------------------------------------------------\n"++
      "                  The Granule Help Menu                                         \n"++
      "-----------------------------------------------------------------------------------\n"++
      ":help             (:h)  Display the help menu\n"++
      ":quit             (:q)  Quit Granule\n"++
      ":show <term>      (:s)  Display the Abstract Syntax Type of a term\n"++
      ":unfold <term>    (:u)  Unfold the expression into one without toplevel definition.\n"++ 
      ":dump             (:d)  Display the context\n"++
      ":load <filepath>  (:l)  Load an external file into the context\n"++
      "-----------------------------------------------------------------------------------"
          
repl :: IO ()
repl = do
  evalStateT (runInputT defaultSettings loop) emptyQ
   where 
       loop :: InputT REPLStateIO ()
       loop = do           
           minput <- getInputLine "Granule> "
           case minput of
               Nothing -> return ()
               Just [] -> loop
               Just input | input == ":q" || input == ":quit"
                              -> liftIO $ putStrLn "Leaving Granule." >> return ()
                          | input == ":h" || input == ":help"
                              -> (liftIO $ putStrLn helpMenu) >> loop                                 
                          | otherwise -> (lift.handleCMD $ input) >> loop