{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Interpreter.HeapModel where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Context
import Language.Granule.Utils

import Control.Monad.State

--import Debug.Trace

-- Represent symbolic values in the heap semantics
data Symbolic = Symbolic Id
  deriving Show

instance Pretty Symbolic where
  pretty (Symbolic x) = "?" ++ internalName x

-- Some type alises
type Val   = Value Symbolic ()
type Grade = Type
-- Heap map
type Heap = Ctxt (Grade, Expr Symbolic ())
  -- Ctxt (Grade, (Ctxt Type, Expr () (), Type))

isSVal :: Expr Symbolic () -> Bool
isSVal (Val _ _ _ (Ext _ (Symbolic _))) = True
isSVal _ = False

for :: [a] -> (a -> b) -> [b]
for = flip map

-- Stubs
heapEval :: AST Symbolic () -> IO (Maybe Val)
heapEval _ = return Nothing

heapEvalDefs :: [Def Symbolic ()] -> Id -> IO (Ctxt Val)
heapEvalDefs defs defName = return []

-- Examples
-- (\([x] : Int [2]) -> x)
-- (\([x] : Int [2]) -> \([y] : Int [0]) -> x)
-- (\(f : (Int -> (Int -> Int))) -> \(g : Int -> Int) -> \([x] : Int [2]) -> (f x) (g x))
-- (\([f] : (Int [Lo] -> Int) [Lo]) -> \(g : (Int [Hi] -> Int)) -> \([x] : Int [Hi]) -> g [f [x]])

-- Key hook in for now
heapEvalJustExprAndReport :: (?globals :: Globals) => Expr Symbolic () -> Int -> Maybe String
heapEvalJustExprAndReport e steps =
    Just (concatMap report res)
  where
    res = evalState (heapEvalJustExpr e steps) 0
    report (expr, (heap, grades, inner)) =
        "Expr = " ++ pretty expr
       ++ "\n Heap = " ++ prettyHeap heap
       ++ "\n Output grades = " ++ pretty grades
       ++ "\n Embedded context = " ++ pretty inner
       ++ "\n"
    prettyHeap = pretty

heapEvalJustExpr :: Expr Symbolic () ->  Int -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]
heapEvalJustExpr e steps =
  multiSmallHeapRedux heap e' (TyGrade Nothing 1) steps
   where
    (heap, e') = buildInitialHeap e

buildInitialHeap :: Expr Symbolic () -> (Heap, Expr Symbolic ())
-- Graded abstraction
buildInitialHeap (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ v)) (Just (Box r a)) e)) =
    (h0 : heap, e')
  where
     h0        = (v, (r, (Val nullSpanNoFile () False (Ext () (Symbolic v)))))
     (heap, e') = buildInitialHeap e
-- Linear abstraction treated as graded 1
buildInitialHeap (Val _ _ _ (Abs _ (PVar _ _ _ v) (Just a) e)) =
    (h0 : heap, e')
  where
     h0        = (v, (TyGrade Nothing 1, (Val nullSpanNoFile () False (Var () v))))
     (heap, e') = buildInitialHeap e

buildInitialHeap e = ([], e)

ctxtPlusZip :: Ctxt Grade -> Ctxt Grade -> Ctxt Grade
ctxtPlusZip [] ctxt' = ctxt'
ctxtPlusZip ((i, g) : ctxt) ctxt' =
  case lookupAndCutout i ctxt' of
    Just (ctxt', g') -> (i, TyInfix TyOpPlus g g') : ctxtPlusZip ctxt ctxt'
    Nothing -> (i, g) : ctxtPlusZip ctxt ctxt'

-- Multi-step relation
multiSmallHeapRedux :: Heap -> Expr Symbolic () -> Grade -> Int -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]
multiSmallHeapRedux heap e r 0 = return [(e, (heap, [], []))]
multiSmallHeapRedux heap e r steps = do
  res <- smallHeapRedux heap e r
  ress <-
    mapM (\(b1, (heap', u', gamma1)) -> do
      res' <- multiSmallHeapRedux heap' b1 r (steps - 1)
      return $ map (\(b, (heap'', u'', gamm2)) -> (b, (heap'', ctxtPlusZip u' u'', gamma1 ++ gamm2))) res') res
  return $ concat ress

-- Functionalisation of the main small-step reduction relation
smallHeapRedux :: Heap -> Expr Symbolic () -> Grade -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]

-- [Small-Var]
smallHeapRedux heap (Val _ _ _ (Var _ x)) r = do
  case lookupAndCutout x heap of
    Just (heap', (rq, aExpr)) ->
    --Just (heap', (rq, (gamma, aExpr, aType))) ->
      let
        gammaOut    = []
        resourceOut = [(x, r)]
        -- Represent (possibly undefined resource minus here)
        --heapHere    = (x, (TyInfix TyOpMinus rq r, (gamma, aExpr, aType)))
        heapHere    = (x, (TyInfix TyOpMinus rq r, aExpr))

      in return [(aExpr, (heapHere : heap', resourceOut , gammaOut))]

    -- Heap not well-formed
    Nothing -> return []

-- [Small-AppBeta] adapted to a Granule graded beta redux, e.g., (\[x] -> a) [b]
smallHeapRedux heap
    (App _ _ _ (Val _ _ _ (Abs _ (PVar _ _ _ y) (Just (Box q aType')) a)) (Val s _ _ (Promote _ b))) r = do
  -- fresh variable
  st <- get
  let x = mkId $ "x" ++ show st
  put $ st+1
  --
  let heap' = (x, (TyInfix TyOpTimes r q, b)) : heap
  return [(subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , TyInfix TyOpTimes r q)]))]

-- [Pair R] (specialised)
smallHeapRedux heap
     (App s a b (App s' a' b' (Val s'' a'' b'' (Constr a3 (internalName -> ",") [])) e1) e2) r | isSVal e1 = do
 -- Evaluate right
    res <- smallHeapRedux heap e2 r
    return $ for res
              (\(e2', env)
                    -> (App s a b (App s' a' b' (Val s'' a'' b'' (Constr a3 (mkId ",") [])) e1) e2'
                      , env))

-- [Pair L] (specialised)
smallHeapRedux heap
     (App s a b (App s' a' b' (Val s'' a'' b'' (Constr a3 (internalName -> ",") [])) e1) e2) r = do
 -- Evaluate left
    res <- smallHeapRedux heap e1 r
    return $ for res
              (\(e1', env)
                    -> (App s a b (App s' a' b' (Val s'' a'' b'' (Constr a3 (mkId ",") [])) e1') e2
                      , env))

-- [Small-AppL]
smallHeapRedux heap (App s a b e1 e2) r = do
  res <- smallHeapRedux heap e1 r
  return $ map (\(e1', (h, resourceOut, gammaOut)) -> (App s a b e1' e2, (h, resourceOut, gammaOut))) res


-- Catch all
smallHeapRedux heap e t =
  return [(e, (heap, [], []))]