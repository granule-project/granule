{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Repl.Repl where

import Control.Monad.State
import System.Console.Haskeline
--import System.Console.Haskeline.MonadException    
--import System.Exit
--import qualified Data.Map.Strict as M

import Repl.Queue
import Syntax.Parser
import Syntax.Lexer
import Syntax.Pretty
--import Eval
import Syntax.Expr


type Qelm = (Id, Expr)
type REPLStateIO = StateT (Queue (QDefName, QDefDef)) IO

instance MonadException m => MonadException (StateT (Queue (QDefName, QDefDef)) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'                       

data QDefName = RVar Id  | DefName Id 
    deriving (Show, Eq)
data QDefDef  = DefTerm Expr
    deriving Show


getQDefM :: (QDefName, QDefDef) -> REPLStateIO (Id, Expr)
getQDefM e@(RVar x, DefTerm t) = return (x , t)
getQDefM e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "++(prettyDef e)

getQDef :: (QDefName, QDefDef) -> (Id, Expr)
getQDef e@(RVar x, DefTerm t) = (x , t)
getQDef e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "++(prettyDef e)

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
prettyDef elem = let (a,t) = getQDef elem in "let "++(sourceName a)++" = "++(pretty t)
    
pop :: REPLStateIO (QDefName, QDefDef)
pop = get >>= return.headQ

push :: (QDefName, QDefDef) -> REPLStateIO ()
push t = do
  q <- get
  put (q `snoc` t)

-- **** 
unfoldQueue :: (Queue Qelm) -> (Queue Qelm)
unfoldQueue q = fixQ q emptyQ step
 where
   step :: (Id, Expr) -> t -> Queue Qelm -> Queue Qelm
   step e@(x,t) _ r = (mapQ (substDef t x) r) `snoc` e
    where
      substDef :: Expr -> Id -> Qelm -> Qelm
      substDef x t (y, t') = (y, subst x t t')  
      
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




handleCMD :: String -> REPLStateIO ()
handleCMD "" = return ()
handleCMD s =    
   case (defs $ scanTokens s) of
    l -> handleLine l
  where      
    handleLine l = undefined
      

     
   
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