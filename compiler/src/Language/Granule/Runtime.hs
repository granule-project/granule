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

--------------------------------------------------------------------------------
-- Mutable arrays
--------------------------------------------------------------------------------

data FloatArray = FloatArray { grLength :: Int
                             , grPtr    :: Ptr Float
                             }

{-# NOINLINE newFloatArray #-}
newFloatArray :: Int -> FloatArray
newFloatArray size = unsafePerformIO $ do
  ptr <- mallocArray size
  return $ FloatArray size ptr

{-# NOINLINE writeFloatArray #-}
writeFloatArray :: FloatArray -> Int -> Float -> FloatArray
writeFloatArray a i v =
  if i >= grLength a
  then error "array index out of bounds"
  else unsafePerformIO $ do
    pokeElemOff (grPtr a) i v
    return a

{-# NOINLINE readFloatArray #-}
readFloatArray :: FloatArray -> Int -> (Float, FloatArray)
readFloatArray a i =
  if i >= grLength a
  then error "array index out of bounds"
  else unsafePerformIO $ do
    v <- peekElemOff (grPtr a) i
    return (v,a)

lengthFloatArray :: FloatArray -> (Int, FloatArray)
lengthFloatArray a = (grLength a, a)

{-# NOINLINE deleteFloatArray #-}
deleteFloatArray :: FloatArray -> ()
deleteFloatArray FloatArray{grPtr} =
  unsafePerformIO $ free grPtr
