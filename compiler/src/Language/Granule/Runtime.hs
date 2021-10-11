-- | Implementations of builtin Granule functions in Haskell

{-# LANGUAGE NamedFieldPuns, Strict #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
module Language.Granule.Runtime where

import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Foreign.Marshal.Alloc
import System.IO
import qualified Data.Array.IO as MA
import Criterion.Main
import System.IO.Silently

--------------------------------------------------------------------------------
-- Benchmarking
--------------------------------------------------------------------------------

data BenchList =
    BenchGroup String BenchList BenchList
  | Bench Int String (Int -> IO ()) BenchList
  | Done

mkIOBenchMain :: BenchList -> IO ()
mkIOBenchMain ns = defaultMain (go ns) -- map (\(n,s,f) -> bench s $ nfIO $ f n) ns
  where go (Bench n s f next) = bench s (nfAppIO (silence . f) n) : go next
        go (BenchGroup str benchs next) = bgroup str (go benchs) : go next
        go Done = []

--------------------------------------------------------------------------------
-- I/O
--------------------------------------------------------------------------------

fromStdin :: IO String
fromStdin = do
  putStr "> "
  hFlush stdout
  getLine

toStdout :: String -> IO ()
toStdout = putStr

toStderr :: String -> IO ()
toStderr = hPutStr stderr

readInt :: IO Int
readInt = do
  putStr "> "
  hFlush stdout
  read <$> getLine

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

showChar :: Char -> String
showChar c = [c]

intToFloat :: Int -> Float
intToFloat = fromIntegral

showInt :: Int -> String
showInt = show

showFloat :: Float -> String
showFloat = show

--------------------------------------------------------------------------------
-- Mutable arrays
--------------------------------------------------------------------------------

data FloatArray = FloatArray { grLength :: Int
                             , grPtr    :: Ptr Float
                             , grArr    :: Maybe (MA.IOArray Int Float)
                             }

{-# NOINLINE newFloatArray #-}
newFloatArray :: Int -> FloatArray
newFloatArray size = unsafePerformIO $ do
  ptr <- mallocArray (size + 1)
  return $ FloatArray (size + 1) ptr Nothing

{-# NOINLINE newFloatArray' #-}
newFloatArray' :: Int -> FloatArray
newFloatArray' size = unsafePerformIO $ do
  arr <- MA.newArray (0,size) 0.0
  let ptr = nullPtr
  return $ FloatArray (size + 1) ptr (Just arr)

{-# NOINLINE writeFloatArray #-}
writeFloatArray :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else unsafePerformIO $ do
    () <- pokeElemOff (grPtr a) i v
    return a

{-# NOINLINE writeFloatArray' #-}
writeFloatArray' :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray' a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case grArr a of
    Nothing -> error "expected non-unique array"
    Just arr -> unsafePerformIO $ do
      a' <- MA.mapArray id arr
      () <- MA.writeArray a' i v
      return $ FloatArray (grLength a) nullPtr (Just a')

{-# NOINLINE readFloatArray #-}
readFloatArray :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray a i =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else unsafePerformIO $ do
    v <- peekElemOff (grPtr a) i
    return (v,a)

{-# NOINLINE readFloatArray' #-}
readFloatArray' :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray' a i =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case grArr a of
    Nothing -> error "expected non-unique array"
    Just arr -> unsafePerformIO $ do
      e <- MA.readArray arr i
      return (e,a)

lengthFloatArray :: FloatArray -> (Int, FloatArray)
lengthFloatArray a = (grLength a, a)

{-# NOINLINE deleteFloatArray #-}
deleteFloatArray :: FloatArray -> ()
deleteFloatArray FloatArray{grPtr} =
  unsafePerformIO $ free grPtr

--------------------------------------------------------------------------------
-- Uniqueness monadic operations
--------------------------------------------------------------------------------

uniqueReturn :: a -> a
uniqueReturn = id

uniqueBind :: (a -> b) -> a -> b
uniqueBind f = f

uniquePush :: (a,b) -> (a,b)
uniquePush = id

uniquePull :: (a,b) -> (a,b)
uniquePull = id
