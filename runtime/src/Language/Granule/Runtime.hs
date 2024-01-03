-- | Implementations of builtin Granule functions in Haskell

{-# LANGUAGE NamedFieldPuns, Strict, NoImplicitPrelude, TypeFamilies,
             DataKinds, GADTs #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-warn-unused-binds #-}
module Language.Granule.Runtime
  (
    -- Granule runtime-specific data structures
    FloatArray(..), BenchList(..), RuntimeData(..)

    -- Granule runtime-specific procedures
  , pure
  , mkIOBenchMain,fromStdin,toStdout,toStderr,timeDate,readInt,showChar,intToFloat
  , showInt,showFloat, charToInt, charFromInt, stringAppend
  , newFloatArray,newFloatArrayI,writeFloatArray,writeFloatArrayI
  , readFloatArray,readFloatArrayI,lengthFloatArray,deleteFloatArray,copyFloatArray'
  , uniqueReturn,uniqueBind,uniquePush,uniquePull,uniquifyFloatArray,borrowFloatArray
  , newFloatArraySafe,newFloatArrayISafe,writeFloatArraySafe,writeFloatArrayISafe
  , readFloatArraySafe,readFloatArrayISafe,deleteFloatArraySafe,copyFloatArraySafe
  , uniquifyFloatArraySafe,borrowFloatArraySafe
  , newRefSafe, freezeRefSafe, swapRefSafe, readRefSafe, copyRefSafe
  , cap, Cap(..), Capability(..), CapabilityType

  -- Re-exported from Prelude
  , String, Int, IO, Float, Maybe(..), Show(..), Char, getLine
  , putStr, read, (<$>) , fromIntegral, Monad(..)
  , ($), error, (>), (++), id, Num(..), (.)
  , pack, Text
  ) where

import Foreign.Marshal.Array ( callocArray )
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
import Data.Time.Clock
import qualified Data.IORef as MR

-- ^ Eventually this can be expanded with other kinds of runtime-managed data
data RuntimeData a = FA FloatArray | PR (PolyRef a)

-- ^ Granule calls doubles floats
type Float = Double

-- ^ Granule calls Text String
type String = Text

pure :: Monad m => a -> m a
pure = return

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

timeDate :: () -> IO String
timeDate () = getCurrentTime >>= (return . pack . show)

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

data PolyRef a =
  HaskellRef {
    haskRef :: MR.IORef a
  }

{-# NOINLINE newFloatArray #-}
newFloatArray :: Int -> FloatArray
newFloatArray = unsafePerformIO . newFloatArraySafe

newFloatArraySafe :: Int -> IO FloatArray
newFloatArraySafe size = do
  ptr <- callocArray size
  return $ PointerArray size ptr

{-# NOINLINE newRef #-}
newRef :: a -> PolyRef a
newRef = unsafePerformIO . newRefSafe

newRefSafe :: a -> IO (PolyRef a)
newRefSafe v = do
  r <- MR.newIORef v
  return $ HaskellRef r

{-# NOINLINE newFloatArrayI #-}
newFloatArrayI :: Int -> FloatArray
newFloatArrayI = unsafePerformIO . newFloatArrayISafe

newFloatArrayISafe :: Int -> IO FloatArray
newFloatArrayISafe size = do
  arr <- MA.newArray (0,size-1) 0.0
  return $ HaskellArray size arr

{-# NOINLINE writeFloatArray #-}
writeFloatArray :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray a i v = unsafePerformIO $ writeFloatArraySafe a i v

writeFloatArraySafe :: FloatArray -> Int -> Float -> IO FloatArray
writeFloatArraySafe a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    HaskellArray{} -> error "expected unique array"
    PointerArray len ptr -> do
      () <- pokeElemOff ptr i v
      return $ PointerArray len ptr

{-# NOINLINE writeFloatArrayI #-}
writeFloatArrayI :: FloatArray -> Int -> Float -> FloatArray
writeFloatArrayI a i v = unsafePerformIO $ writeFloatArrayISafe a i v

writeFloatArrayISafe :: FloatArray -> Int -> Float -> IO FloatArray
writeFloatArrayISafe a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> do
      arr' <- MA.mapArray id arr
      () <- MA.writeArray arr' i v
      return $ HaskellArray len arr'

{-# NOINLINE swapRef #-}
swapRef :: PolyRef a -> a -> (a, PolyRef a)
swapRef r v = unsafePerformIO $ swapRefSafe r v

swapRefSafe :: PolyRef a -> a -> IO (a, PolyRef a)
swapRefSafe HaskellRef{haskRef} v = do
  x <- MR.readIORef haskRef
  MR.writeIORef haskRef v
  return $ (x, HaskellRef haskRef)

{-# NOINLINE readRef #-}
readRef :: PolyRef a -> (a, PolyRef a)
readRef = unsafePerformIO . readRefSafe

readRefSafe :: PolyRef a -> IO (a, PolyRef a)
readRefSafe HaskellRef{haskRef} = do
  x <- MR.readIORef haskRef
  return $ (x, HaskellRef haskRef)

{-# NOINLINE readFloatArray #-}
readFloatArray :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray a i = unsafePerformIO $ readFloatArraySafe a i

readFloatArraySafe :: FloatArray -> Int -> IO (Float, FloatArray)
readFloatArraySafe a i =
  if i > grLength a
  then error $ "readFloatArray index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    HaskellArray{} -> error "expected unique array"
    PointerArray len ptr -> do
      v <- peekElemOff ptr i
      return (v,a)

{-# NOINLINE readFloatArrayI #-}
readFloatArrayI :: FloatArray -> Int -> (Float, FloatArray)
readFloatArrayI a i = unsafePerformIO $ readFloatArrayISafe a i

readFloatArrayISafe :: FloatArray -> Int -> IO (Float, FloatArray)
readFloatArrayISafe a i =
  if i > grLength a
  then error $ "readFloatArrayI index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray _ arr -> do
      e <- MA.readArray arr i
      return (e,a)

lengthFloatArray :: FloatArray -> (Int, FloatArray)
lengthFloatArray a = (grLength a, a)

{-# NOINLINE deleteFloatArray #-}
deleteFloatArray :: FloatArray -> ()
deleteFloatArray = unsafePerformIO . deleteFloatArraySafe

deleteFloatArraySafe :: FloatArray -> IO ()
deleteFloatArraySafe PointerArray{grPtr} =
  free grPtr
deleteFloatArraySafe HaskellArray{grArr} =
  void (MA.mapArray (const undefined) grArr)

{-# NOINLINE freezeRef #-}
freezeRef :: PolyRef a -> a
freezeRef = unsafePerformIO . freezeRefSafe

freezeRefSafe :: PolyRef a -> IO a
freezeRefSafe HaskellRef{haskRef} =
  MR.readIORef haskRef

{-# NOINLINE copyFloatArray' #-}
copyFloatArray' :: FloatArray -> FloatArray
copyFloatArray' = unsafePerformIO . copyFloatArraySafe

copyFloatArraySafe :: FloatArray -> IO FloatArray
copyFloatArraySafe a =
  case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> do
      arr' <- MA.mapArray id arr
      return $ uniquifyFloatArray $ HaskellArray len arr'

{-# NOINLINE copyRef #-}
copyRef :: PolyRef a -> PolyRef a
copyRef = unsafePerformIO . copyRefSafe

copyRefSafe :: PolyRef a -> IO (PolyRef a)
copyRefSafe HaskellRef{haskRef} = do
  val <- MR.readIORef haskRef
  haskRef' <- MR.newIORef val
  return $ HaskellRef haskRef'

{-# NOINLINE uniquifyFloatArray #-}
uniquifyFloatArray :: FloatArray -> FloatArray
uniquifyFloatArray = unsafePerformIO . uniquifyFloatArraySafe

uniquifyFloatArraySafe :: FloatArray -> IO FloatArray
uniquifyFloatArraySafe a =
  case a of
    PointerArray{} -> error "expected non-unique array"
    HaskellArray len arr -> do
      arr' <- newFloatArraySafe len
      forM_ [0..(len-1)] $ \i -> do
        v <- MA.readArray arr i
        pokeElemOff (grPtr arr') i v
      return arr'

{-# NOINLINE borrowFloatArray #-}
borrowFloatArray :: FloatArray -> FloatArray
borrowFloatArray = unsafePerformIO . borrowFloatArraySafe

borrowFloatArraySafe :: FloatArray -> IO FloatArray
borrowFloatArraySafe a =
  case a of
    HaskellArray{} -> error "expected unique array"
    PointerArray len ptr -> do
      arr' <- newFloatArrayISafe len
      forM_ [0..(len-1)] $ \i -> do
        v <- peekElemOff ptr i
        MA.writeArray (grArr arr') i v
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

--------------------------------------------------------------------------------
-- Capabilities
--------------------------------------------------------------------------------

-- Emulate dependent types
data Cap = ConsoleTag | TimeDateTag

data Capability (c :: Cap) where
    Console :: Capability 'ConsoleTag
    TimeDate :: Capability 'TimeDateTag

type family CapabilityType (c :: Cap)
type instance CapabilityType 'ConsoleTag = Text -> ()
type instance CapabilityType 'TimeDateTag = () -> Text

{-# NOINLINE cap #-}
cap :: Capability cap -> () -> CapabilityType cap
cap Console ()  = \x -> unsafePerformIO $ toStdout $ x
cap TimeDate () = \() -> unsafePerformIO $ timeDate ()