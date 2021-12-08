-- | Implementations of builtin Granule functions in Haskell

{-# LANGUAGE NamedFieldPuns, Strict, NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
module Language.Granule.Runtime
  (
    -- Granule runtime-specific data structures
    FloatArray(..), BenchList(..), RuntimeData

    -- Granule runtime-specific procedures
  , mkIOBenchMain,fromStdin,toStdout,toStderr,readInt,showChar,intToFloat
  , showInt,showFloat, charToInt, charFromInt, stringAppend
  , newFloatArray,newFloatArray',writeFloatArray,writeFloatArray'
  , readFloatArray,readFloatArray',lengthFloatArray,deleteFloatArray,copyFloatArray'
  , uniqueReturn,uniqueBind,uniquePush,uniquePull,uniquifyFloatArray

  -- Re-exported from Prelude
  , String, Int, IO, Float, Maybe(..), Show(..), Char, getLine
  , putStr, read, (<$>) , fromIntegral, Monad(..)
  , ($), error, (>), (++), id, Num(..), (.)
  ) where

import Foreign.Marshal.Array ( mallocArray )
import Foreign.Ptr ( Ptr )
import Foreign.Storable ( Storable(peekElemOff, pokeElemOff) )
import System.IO.Unsafe ( unsafePerformIO )
import Foreign.Marshal.Alloc ( free )
import System.IO ( hFlush, stderr, stdout )
import qualified Data.Array.IO as MA
import Criterion.Main ( defaultMain, bench, bgroup, nfAppIO )
import System.IO.Silently ( silence )
import Prelude
    ( Int, IO, Double, Maybe(..), Show(..), Char, read, fromEnum, toEnum
    , (<$>), (<>), fromIntegral, ($), error, (>), (++), id, Num (..), (.) )
import Control.Monad
import GHC.Err (undefined)
import Data.Function (const)
import Data.Text
import Data.Text.IO

-- ^ Eventually this can be expanded with other kinds of runtime-managed data
type RuntimeData = FloatArray

-- ^ Granule calls doubles floats
type Float = Double

-- ^ Granule calls Text String
type String = Text

--------------------------------------------------------------------------------
-- Benchmarking
--------------------------------------------------------------------------------

data BenchList =
    BenchGroup String BenchList BenchList
  | Bench Int String (Int -> IO ()) BenchList
  | Done

mkIOBenchMain :: BenchList -> IO ()
mkIOBenchMain ns = defaultMain (go ns)
  where go (Bench n s f next) = bench (unpack s) (nfAppIO (silence . f) n) : go next
        go (BenchGroup str benchs next) = bgroup (unpack str) (go benchs) : go next
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
toStderr = let red x = "\ESC[31;1m" <> x <> "\ESC[0m" in (hPutStr stderr) . red

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

readInt :: String -> Int
readInt s =
  if null s
  then 0
  else read $ unpack s

showChar :: Char -> String
showChar = singleton

charToInt :: Char -> Int
charToInt = fromEnum

charFromInt :: Int -> Char
charFromInt = toEnum

intToFloat :: Int -> Float
intToFloat = fromIntegral

showInt :: Int -> String
showInt = pack . show

showFloat :: Float -> String
showFloat = pack . show

--------------------------------------------------------------------------------
-- String operations
--------------------------------------------------------------------------------

stringAppend :: String -> String -> String
stringAppend = (<>)

--------------------------------------------------------------------------------
-- Mutable arrays
--------------------------------------------------------------------------------

data FloatArray =
  HaskellArray {
    -- | Length of Haskell array
    grLength :: Int,
    -- | An ordinary Haskell IOArray
    grArr :: MA.IOArray Int Float } |
  PointerArray {
    -- | Length of the array in memory
    grLength :: Int,
    -- | Pointer to a block of memory
    grPtr :: Ptr Float }

{-# NOINLINE newFloatArray #-}
newFloatArray :: Int -> FloatArray
newFloatArray size = unsafePerformIO $ do
  ptr <- mallocArray (size + 1)
  return $ PointerArray (size + 1) ptr

{-# NOINLINE newFloatArray' #-}
newFloatArray' :: Int -> FloatArray
newFloatArray' size = unsafePerformIO $ do
  arr <- MA.newArray (0,size) 0.0
  return $ HaskellArray (size + 1) arr

{-# NOINLINE writeFloatArray #-}
writeFloatArray :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    HaskellArray{} -> error "expected unique array"
    PointerArray len ptr -> unsafePerformIO $ do
      () <- pokeElemOff ptr i v
      return $ PointerArray len ptr

{-# NOINLINE writeFloatArray' #-}
writeFloatArray' :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray' a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> unsafePerformIO $ do
      arr' <- MA.mapArray id arr
      () <- MA.writeArray arr' i v
      return $ HaskellArray len arr'

{-# NOINLINE readFloatArray #-}
readFloatArray :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray a i =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    HaskellArray{} -> error "expected unique array"
    PointerArray len ptr -> unsafePerformIO $ do
      v <- peekElemOff ptr i
      return (v,a)

{-# NOINLINE readFloatArray' #-}
readFloatArray' :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray' a i =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray _ arr -> unsafePerformIO $ do
      e <- MA.readArray arr i
      return (e,a)

lengthFloatArray :: FloatArray -> (Int, FloatArray)
lengthFloatArray a = (grLength a, a)

{-# NOINLINE deleteFloatArray #-}
deleteFloatArray :: FloatArray -> ()
deleteFloatArray PointerArray{grPtr} =
  unsafePerformIO $ free grPtr
deleteFloatArray HaskellArray{grArr} =
  unsafePerformIO $ void (MA.mapArray (const undefined) grArr)

{-# NOINLINE copyFloatArray' #-}
copyFloatArray' :: FloatArray -> FloatArray
copyFloatArray' a =
  case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> unsafePerformIO $ do
      arr' <- MA.mapArray id arr
      return $ HaskellArray len arr'


uniquifyFloatArray :: FloatArray -> FloatArray
uniquifyFloatArray a =
  case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> unsafePerformIO $ do
      let arr' = newFloatArray (len - 1)
      forM_ [0..len - 1] $ \i -> do
        v <- MA.readArray arr i
        pokeElemOff (grPtr arr') i v
      return arr'

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
