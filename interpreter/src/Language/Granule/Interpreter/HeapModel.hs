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
import Language.Granule.Interpreter.Desugar

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
heapEvalJustExprAndReport :: (?globals :: Globals) => [Def Symbolic ()] -> Expr Symbolic () -> Int -> Maybe String
heapEvalJustExprAndReport defs e steps =
    Just (concatMap report res)
  where
    res = evalState (heapEvalJustExpr defs e steps) 0
    report (expr, (heap, grades, inner)) =
        "Expr = " ++ pretty expr
       ++ "\n Heap = " ++ prettyHeap heap
       ++ "\n Output grades = " ++ pretty grades
       ++ "\n Embedded context = " ++ pretty inner
       ++ "\n"
    prettyHeap = pretty

heapEvalJustExpr :: (?globals :: Globals)
   => [Def Symbolic ()] -> Expr Symbolic () ->  Int -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]
heapEvalJustExpr defs e steps =
  multiSmallHeapRedux defCtxt heap e' (TyGrade Nothing 1) steps
   where
     defCtxt = map (\def -> (defId def, desugar def)) defs
     (heap, e') = buildInitialHeap e

buildInitialHeap :: (?globals :: Globals)
   => Expr Symbolic () -> (Heap, Expr Symbolic ())
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
     h0        = (v, (TyGrade Nothing 1, (Val nullSpanNoFile () False (Ext () (Symbolic v)))))
     (heap, e') = buildInitialHeap e

buildInitialHeap e = ([], e)

ctxtPlusZip :: Ctxt Grade -> Ctxt Grade -> Ctxt Grade
ctxtPlusZip [] ctxt' = ctxt'
ctxtPlusZip ((i, g) : ctxt) ctxt' =
  case lookupAndCutout i ctxt' of
    Just (ctxt', g') -> (i, TyInfix TyOpPlus g g') : ctxtPlusZip ctxt ctxt'
    Nothing -> (i, g) : ctxtPlusZip ctxt ctxt'

-- Multi-step relation
multiSmallHeapRedux :: (?globals :: Globals)
   => Ctxt (Def Symbolic ()) -> Heap -> Expr Symbolic () -> Grade -> Int -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]
multiSmallHeapRedux defs heap e r 0 = return [(e, (heap, [], []))]
multiSmallHeapRedux defs heap e r steps = do
  res <- smallHeapRedux defs heap e r
  ress <-
    mapM (\(b1, (heap', u', gamma1)) -> do
      res' <- multiSmallHeapRedux defs heap' b1 r (steps - 1)
      return $ map (\(b, (heap'', u'', gamm2)) -> (b, (heap'', ctxtPlusZip u' u'', gamma1 ++ gamm2))) res') res
  return $ concat ress

-- Functionalisation of the main small-step reduction relation
smallHeapRedux :: (?globals :: Globals)
               => Ctxt (Def Symbolic ()) -> Heap -> Expr Symbolic () -> Grade -> State Integer [(Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))]

-- [Small-Var]
smallHeapRedux defs heap (Val _ _ _ (Var _ x)) r = do
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

    -- Heap does not contain the variable, so maybe it's a definition we are
    -- getting
    Nothing ->
      case lookup x defs of
        -- Invalid heap and definition environment
        Nothing -> return []
        -- Since the desugaring has been run there should be only one equations
        Just (Def _ _ _ (EquationList _ _ _ [Equation _ _ _ _ [] expr]) _) ->
          -- Substitute body of the function here
          return [(expr, (heap, [], []))]
        Just d ->
          error $ "Internal bug: def was in the wrong format for the heap model: " ++ pretty d

-- -- [Small-AppBeta] adapted to a Granule graded beta redux, e.g., (\[x] -> a) [b]
smallHeapRedux defs heap
    (App _ _ _ (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ y)) (Just (Box q aType')) a)) (Val s _ _ (Promote _ b))) r = do
  --
  x <- freshVariable y
  --
  let heap' = (x, (TyInfix TyOpTimes r q, b)) : heap
  return [(subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , TyInfix TyOpTimes r q)]))]

-- [Small-AppBeta] [NO GRADE ANNOTATIONS] adapted to a Granule graded beta redux, e.g., (\[x] -> a) [b]
smallHeapRedux defs heap
    (App _ _ _ (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ y)) _ a)) (Val s _ _ (Promote _ b))) r = do
  --
  x <- freshVariable y
  --
  let heap' = (x, (r, b)) : heap
  return [(subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , r)]))]

-- [Small-AppBetaLinear] - Linear beta-redux, because Granule
smallHeapRedux defs heap
    (App _ _ _ (Val s _ _ (Abs _ (PVar _ _ _ y) _ a)) b) r = do
  --
  x <- freshVariable y
  --
  let heap' = (x, (r, b)) : heap
  return [(subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , r)]))]

-- [App beta]
smallHeapRedux defs heap (App s a b (Val s' a' b' (Constr a'' id vs)) (Val _ _ _ v)) r | isValue v =
  return [(Val s' a' b' (Constr a'' id (vs ++ [v])), (heap, [], []))]

-- [App Value]
smallHeapRedux defs heap (App s a b (Val s' a' b' (Constr a'' id vs)) e) r = do
  res <- smallHeapRedux defs heap e r
  return $ for res (\(e', env) -> (App s a b (Val s' a' b' (Constr a'' id vs)) e', env))

-- [Small-AppL]
smallHeapRedux defs heap (App s a b e1 e2) r = do
  res <- smallHeapRedux defs heap e1 r
  return $ map (\(e1', (h, resourceOut, gammaOut)) -> (App s a b e1' e2, (h, resourceOut, gammaOut))) res

-- [Case-Sum-Beta] Matches Left-Right patterns for either
smallHeapRedux defs heap
   (Case s a b (App _ _ _ (Val _ _ _ (Constr _ (internalName -> constr) [])) e)
        [(PConstr _ _ _ (internalName -> "Left") [PVar _ _ _ varl], el)
        ,(PConstr _ _ _ (internalName -> "Right") [PVar _ _ _ varr], er)]) r = do

    -- fresh variable
    x <- freshVariable (if constr == "Left" then varl else varr)
    --
     -- A&B and Grade determine `q` from a syntactic grade
     -- We don't have that here (we could get it out of the typing...)
    let q = TyGrade Nothing 1
    let heap' = (x, (TyInfix TyOpTimes r q, e)) : heap
    --
    let resourceOut = ctxtMap (const (TyGrade Nothing 0)) heap
    let embeddedCtxt = [(x , TyInfix TyOpTimes r q)]
    -- Expression is e1 or e2 (with x replaying varl or varr)
    let eFinal = case constr of
                  "Left" -> subst (Val s () False (Var () x)) varl el
                  "Right" -> subst (Val s () False (Var () x)) varr er
                  _ -> undefined
    return [(eFinal, (heap' , resourceOut, embeddedCtxt))]

-- [Case-Product-Beta]
smallHeapRedux defs heap
  (Case s a b (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ (internalName -> ",") [])) e1) e2)
        [(PConstr _ _ _ (internalName -> ",") [PVar _ _ _ var1, PVar _ _ _ var2], e)]) r = do
  -- fresh variables
  x1 <- freshVariable var1
  x2 <- freshVariable var2
  --
  let heap' = (x1, (r, e1)) : (x2, (r, e2)) : heap
  --
  let resourceOut = ctxtMap (const (TyGrade Nothing 0)) heap
  let embeddedCtxt = [(x1 , r), (x2, r)]
  -- Expression is e1 or e2 (with x replaying varl or varr)
  return [(subst (Val s () False (Var () x1)) var1 (subst (Val s () False (Var () x2)) var2 e), (heap' , resourceOut, embeddedCtxt))]

-- [Case-Box-Beta]
smallHeapRedux defs heap
  (Case s a b (Val _ _ _ (Promote _ e)) [(PBox _ _ _ (PVar _ _ _ var), e')]) r = do
  -- fresh variables
  x <- freshVariable var
  --
  let heap' = (x, (r, e)) : heap
  --
  let resourceOut = ctxtMap (const (TyGrade Nothing 0)) heap
  let embeddedCtxt = [(x, r)]
  -- Expression is e1 or e2 (with x replaying varl or varr)
  return [(subst (Val s () False (Var () x)) var e', (heap' , resourceOut, embeddedCtxt))]

-- [Case-cong]
smallHeapRedux defs heap (Case s a b e ps) r = do
  res <- smallHeapRedux defs heap e r
  return $ map (\(e', (h, resourceOut, gammaOut)) -> (Case s a b e' ps, (h, resourceOut, gammaOut))) res

-- -- [Value]
-- smallHeapRedux defs heap (App _ _ _ (Val s' a' b' (Constr a'' id es)) e) r =
--   return $ (Val s' a' b' (Constr a'' id (es ++ [e])), (heap, [], []))

-- Catch all
smallHeapRedux _ heap e t =
  return [(e, (heap, [], []))]

-- Things that cannot be reduced further by this model
isValue :: Value a b -> Bool
isValue Abs{} = True
isValue Promote{} = True
isValue (Constr _ _ vs) = all isValue vs
isValue NumInt{} = True
isValue NumFloat{} = True
isValue CharLiteral{} = True
isValue StringLiteral{} = True
isValue Ext{} = True
isValue _ = False

freshVariable :: Id -> State Integer Id
freshVariable x = do
  st <- get
  let x' = mkId $ (internalName x) ++ "." ++ show st
  put $ st+1
  return x'
