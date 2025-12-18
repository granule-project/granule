{-# OPTIONS_GHC -Wno-orphans -Wno-missing-methods #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.StdError where

instance Num (Double, [Double]) where
  (x, ds) + (x', ds') = (x+x', ds++ds')
  fromInteger n = (fromInteger n, [])

-- Sample standard deviation
stdDeviation :: [Double] -> Double
stdDeviation xs = sqrt (divisor * (sum . map (\x -> (x - mean)**2) $ xs))
  where
   divisor = 1 / ((cast n) - 1)
   n = length xs
   mean = sum xs / (cast n)

cast :: Int -> Double
cast = fromInteger . toInteger

-- Sample standard error
stdError :: [Double] -> Double
stdError []  = 0
stdError [_] = 0
stdError xs  = (stdDeviation xs) / sqrt (cast n)
  where
    n = length xs