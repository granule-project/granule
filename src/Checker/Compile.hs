{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Compile where

import Checker.Coeffects
import Checker.Types
import Syntax.Expr
import Syntax.Pretty

import Data.SBV hiding (kindOf)
import qualified Data.Set as S

-- Compile a coeffect term into its symbolic representation
compile :: Coeffect -> CKind -> [(Id, SCoeffect)] -> SCoeffect
compile (Level n) (CConstr "Level") _ = SLevel . fromInteger . toInteger $ n
compile (CNat Ordered n)  (CConstr "Nat") _
  = SNat Ordered  . fromInteger . toInteger $ n
compile (CNat Discrete n)  (CConstr "Nat=") _
  = SNat Discrete  . fromInteger . toInteger $ n
compile (CReal r) (CConstr "Real")  _ = SReal  . fromRational $ r
compile (CSet xs) (CConstr "Set")   _ = SSet   . S.fromList $ xs
compile (CVar v) k vars =
  case lookup v vars of
   Just cvar -> cvar
   Nothing   ->
    error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars

compile (CPlus n m) k@(CConstr "Set") vars =
  case (compile n k vars, compile m k vars) of
    (SSet s, SSet t) -> SSet $ (S.union s t)
    (n, m) -> error $ "Trying to compile: " ++ show n ++ " + " ++ show m

compile (CPlus n m) k@(CConstr "Level") vars =
  case (compile n k vars, compile m k vars) of
    (SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smax` lev2
    (n, m) -> error $ "Trying to compile: " ++ show n ++ " + " ++ show m

compile (CPlus n m) k vars =
  case (compile n k vars, compile m k vars) of
    (SNat o1 n1, SNat o2 n2) | o1 == o2 -> SNat o1 (n1 + n2)
    (SReal n1, SReal n2) -> SReal $ n1 + n2
    (n, m) -> error $ "Trying to compile: " ++ show n ++ " + " ++ show m

compile (CTimes n m) k@(CConstr "Set") vars =
  case (compile n k vars, compile m k vars) of
    (SSet s, SSet t) -> SSet $ (S.union s t)
    (n, m) -> error $ "Trying to compile: " ++ show n ++ " + " ++ show m

compile (CTimes n m) k@(CConstr "Level") vars =
  case (compile n k vars, compile m k vars) of
    (SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smin` lev2
    (n, m) -> error $ "Trying to compile: " ++ show n ++ " * " ++ show m

compile (CTimes n m) k vars =
  case (compile n k vars, compile m k vars) of
    (SNat o1 n1, SNat o2 n2) | o1 == o2 -> SNat o1 (n1 * n2)
    (SReal n1, SReal n2) -> SReal $ n1 * n2
    (m, n) -> error $ "Trying to compile solver contraints for: "
                      ++ show m ++ " * " ++ show n

compile (CZero (CConstr "Level")) (CConstr "Level") _ = SLevel 0
compile (CZero (CConstr "Nat")) (CConstr "Nat")     _ = SNat Ordered 0
compile (CZero (CConstr "Nat=")) (CConstr "Nat=")   _ = SNat Discrete 0
compile (CZero (CConstr "Q"))  (CConstr "Q")        _ = SReal (fromRational 0)
compile (CZero (CConstr "Set")) (CConstr "Set")     _ = SSet (S.fromList [])

compile (COne (CConstr "Level")) (CConstr "Level") _ = SLevel 1
compile (COne (CConstr "Nat")) (CConstr "Nat")     _ = SNat Ordered 1
compile (COne (CConstr "Nat=")) (CConstr "Nat=")   _ = SNat Discrete 1
compile (COne (CConstr "Q")) (CConstr "Q")         _ = SReal (fromRational 1)
compile (COne (CConstr "Set")) (CConstr "Set")     _ = SSet (S.fromList [])

-- compile (COne (CPoly _)) (CConstr c) vars = compile (COne (CConstr c)) (CConstr c) vars

compile c (CPoly _) _ =
   error $ "Trying to compile a polymorphically kinded " ++ pretty c
compile coeff ckind _ =
   error $ "Can't compile a coeffect: " ++ pretty coeff
        ++ " of kind " ++ show ckind