-- | Implementations of builtin Granule functions in Haskell

{-# LANGUAGE NamedFieldPuns #-}
module Language.Granule.Runtime where

import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Foreign.Marshal.Alloc
import System.IO

--------------------------------------------------------------------------------
-- I/O
--------------------------------------------------------------------------------

data IOElem = Stdout | Stdin | Stderr | Open | Read | Write | IOExcept | Close

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
                             }

{-# NOINLINE newFloatArray #-}
newFloatArray :: Int -> FloatArray
newFloatArray size = unsafePerformIO $ do
  ptr <- mallocArray (size + 1)
  return $ FloatArray (size + 1) ptr

{-# NOINLINE writeFloatArray #-}
writeFloatArray :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray a i v =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else unsafePerformIO $ do
    pokeElemOff (grPtr a) i v
    return a

{-# NOINLINE readFloatArray #-}
readFloatArray :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray a i =
  if i > grLength a
  then error $ "array index out of bounds: " ++ show i ++ " > " ++ show (grLength a)
  else unsafePerformIO $ do
    v <- peekElemOff (grPtr a) i
    return (v,a)

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
