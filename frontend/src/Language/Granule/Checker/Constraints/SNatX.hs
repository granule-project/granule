{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Represents the extended natural numbers in the solver
module Language.Granule.Checker.Constraints.SNatX where

-- import Control.Monad ((<=<))
import Data.SBV
import GHC.Generics (Generic)

newtype SNatX = SNatX { xVal  :: SInteger }
  deriving (Generic, Mergeable)

instance Show SNatX where
  show (SNatX val) = case unliteral val of
    Just (-1) -> "∞"
    Just n    -> show n
    _         -> "<symbolic>"

inf :: SNatX
inf = SNatX $ (literal (-1))

isInf :: SNatX -> SBool
isInf (SNatX n) = n .== -1

instance Num SNatX where
  x + y = ite (isInf x .|| isInf y)
              inf
              (SNatX (xVal x + xVal y))
  x * y = ite ((isInf x .&& y ./= 0) .|| (isInf y .&& x ./= 0)) -- 0 * ∞ = ∞ * 0 = 0
              inf
              (SNatX (xVal x * xVal y))
  x - y = ite (isInf x .|| isInf y)  -- ???
              inf
              (ite (x .< y)          -- monus
                   0
                   (SNatX (xVal x - xVal y)))
  fromInteger = SNatX . literal

instance EqSymbolic SNatX where
  (SNatX a) .== (SNatX b) = a .== b

instance OrdSymbolic SNatX where
  a .< b = ite (isInf b) (ite (isInf a) sFalse sTrue)
         $ ite (isInf a) sFalse
         $ xVal a .< xVal b

representationConstraint :: SInteger -> SBool
representationConstraint v = v .>= -1

freeSNatX :: String -> Symbolic SNatX
freeSNatX nm = do
  v <- sInteger $ nm <> "_xVal"
  constrain $ representationConstraint v
  return $ SNatX v

existsSNatX :: String -> Symbolic SNatX
existsSNatX nm = do
  v <- sbvExists $ nm <> "_xVal"
  constrain $ representationConstraint v
  return $ SNatX v

forallSNatX :: String -> Symbolic SNatX
forallSNatX nm = do
  v <- sbvForall $ nm <> "_xVal"
  constrain $ representationConstraint v
  return $ SNatX v

-- main :: IO ()
-- main = print =<< sat do
--   [x, y, z] <- mapM freeSNatX ["x", "y", "z"]
--   return $ sAnd
--     [ x .== x+1 -- x = ∞
--     , x .== x*y -- y ≠ 0
--     , y .< x    -- y ≠ ∞
--     , z*x .== 0 -- z = 0
--     ]

-- main :: IO ()
-- main = print =<< prove do
--   -- [x, y, z] <- mapM freeSNatX ["x", "y", "z"]
--   y <- existsSNatX_
--   z <- forallSNatX_
--   return $ z .<= y

-- data NatX = NatX (Maybe Integer) deriving Show
--
-- queryNatX :: SNatX -> Query NatX
-- queryNatX (SNatX {isInf, xVal}) = do
--   b <- getValue isInf
--   v <- getValue xVal
--   return $ NatX if b then Nothing else Just v

-- main :: IO ()
-- main = runSMT do
--   [x, y, z] <- mapM freeSNatX ["x", "y", "z"]
--   constrain $ sAnd
--     [ x .== x*y -- x must be 0 or oo, if x |-> oo, then y can't be 0
--     , y .< x    -- nothing smaller than 0, so x |-> oo, and y > 0
--     , z*x .== 0 -- what times oo is 0? z |-> 0
--     ]
--   query do
--     cs <- checkSat
--     case cs of
--       Unk   -> error "Solver said Unknown!"
--       Unsat -> error "Solver said Unsatisfiable!"
--       Sat   -> do
--         mapM_ (io . print <=< queryNatX) [x, y, z]
