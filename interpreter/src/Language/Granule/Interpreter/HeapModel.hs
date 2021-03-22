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

import Data.Foldable
import Data.List (intercalate)

import Control.Monad.State
import Control.Monad.Trans.Maybe

-- import Debug.Trace

-- Represent symbolic values in the heap semantics
data Symbolic = Symbolic Id | ChanPointer Id | Chan [Expr Symbolic ()]
  deriving Show

isChan :: Expr Symbolic b -> Bool
isChan (Val _ _ _ (Ext _ (Chan _))) = True
isChan _ = False

isChanInHeap :: Id -> Heap -> Bool
isChanInHeap x heap =
  case lookup x heap of
    Nothing -> False
    Just (_, expr) -> isChan expr

instance Pretty Symbolic where
  pretty (Symbolic x) = "?" ++ internalName x
  pretty (Chan xs) = "<" ++ intercalate "," (map pretty xs) ++ ">"
  pretty (ChanPointer x) = "*" ++ pretty x

-- Some type alises
type Val   = Value Symbolic ()
type Grade = Type
-- Heap map
type Heap = Ctxt (Grade, Expr Symbolic ())
  -- Ctxt (Grade, (Ctxt Type, Expr () (), Type))

type Process = Expr Symbolic ()

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
    Just (report res)
  where
    (res, (processes, _)) = runState (heapEvalJustExpr defs e steps) ([], 0)
    report (expr, (heap, grades, inner)) =
        "Expr = " ++ pretty expr
       ++ "\n Heap = " ++ prettyHeap heap
       ++ "\n Output grades = " ++ pretty grades
       ++ "\n Processes = " ++ intercalate " | " (map pretty processes)
       -- ++ "\n Embedded context = " ++ pretty inner
       ++ "\n"
    prettyHeap = pretty

heapEvalJustExpr :: (?globals :: Globals)
   => [Def Symbolic ()] -> Expr Symbolic () ->  Int -> State ([Process], Integer) (Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))
heapEvalJustExpr defs e steps =
  multiSmallHeapRedux defCtxt heap e' (TyGrade Nothing 1) steps
   where
     defCtxt = map (\def -> (defId def, desugar def)) defs
     (heap, e') = buildInitialHeap e

buildInitialHeap :: (?globals :: Globals)
   => Expr Symbolic () -> (Heap, Expr Symbolic ())
-- Graded abstraction (special typed rule - cf Grad)
buildInitialHeap (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ v)) (Just (Box r a)) e)) =
    (h0 : heap, e')
  where
     h0        = (v, (r, (Val nullSpanNoFile () False (Ext () (Symbolic v)))))
     (heap, e') = buildInitialHeap e
-- Linear abstraction treated as graded 1
buildInitialHeap (Val _ _ _ (Abs _ p _ e)) =
    (h0 ++ heap, e')
  where
    h0        = toHeap p
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
   => Ctxt (Def Symbolic ()) -> Heap -> Expr Symbolic () -> Grade -> Int -> State ([Process], Integer) (Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))
multiSmallHeapRedux defs heap e r 0 = return (e, (heap, [], []))
multiSmallHeapRedux defs heap e r steps = do
  res@(b1, (heap', u', gamma1)) <- smallHeapRedux defs heap e r
  res'@(b, (heap'', u'', gamm2)) <- multiSmallHeapRedux defs heap' b1 r (steps - 1)
  return (b, (heap'', ctxtPlusZip u' u'', gamma1 ++ gamm2))

-- Functionalisation of the main small-step reduction relation
smallHeapRedux :: (?globals :: Globals)
              => Ctxt (Def Symbolic ())
              -> Heap
              -> Expr Symbolic ()
              -> Grade
              -> State ([Process], Integer) (Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))

smallHeapRedux defs heap t r = do
  res <- runMaybeT (smallHeapReduxAux defs heap t r)
  case res of
    -- No reduction so try to reduce one of the parallel processes
    Nothing -> smallHeapReduxPar defs heap t r
    -- Redux
    Just res' -> return res'

smallHeapReduxAux :: (?globals :: Globals)
              => Ctxt (Def Symbolic ())
              -> Heap
              -> Expr Symbolic ()
              -> Grade
              -> MaybeT (State ([Process], Integer)) (Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))

-- [Small-Var]
smallHeapReduxAux defs heap t@(Val _ _ _ (Var _ x)) r | not (isChanInHeap x heap) = do
  case lookupAndCutout x heap of
    Just (heap', (rq, aExpr)) ->
      if isChan aExpr
        then noRedux
        else
          --Just (heap', (rq, (gamma, aExpr, aType))) ->
            let
              gammaOut    = []
              resourceOut = [(x, r)]
              -- Represent (possibly undefined resource minus here)
              --heapHere    = (x, (TyInfix TyOpMinus rq r, (gamma, aExpr, aType)))
              heapHere    = (x, (TyInfix TyOpMinus rq r, aExpr))

            in return (aExpr, (heapHere : heap', resourceOut , gammaOut))

    -- Heap does not contain the variable, so maybe it's a definition we are
    -- getting
    Nothing ->
      case lookup x defs of
        -- Possibly a built in
        Nothing -> noRedux
        -- Since the desugaring has been run there should be only one equations
        Just (Def _ _ _ (EquationList _ _ _ [Equation _ _ _ _ [] expr]) _) ->
          -- Substitute body of the function here
          return (expr, (heap, [], []))
        Just d ->
          error $ "Internal bug: def was in the wrong format for the heap model: " ++ pretty d

-- -- [Small-AppBeta] adapted to a Granule graded beta redux, e.g., (\[x] -> a) [b]
smallHeapReduxAux defs heap
    (App _ _ _ (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ y)) (Just (Box q aType')) a)) (Val s _ _ (Promote _ b))) r = do
  --
  x <- freshVariable' y
  --
  let heap' = (x, (TyInfix TyOpTimes r q, b)) : heap
  return (subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , TyInfix TyOpTimes r q)]))

-- [Small-AppBeta] [NO GRADE ANNOTATIONS] adapted to a Granule graded beta redux, e.g., (\[x] -> a) [b]
smallHeapReduxAux defs heap
    (App _ _ _ (Val _ _ _ (Abs _ (PBox _ _ _ (PVar _ _ _ y)) _ a)) (Val s _ _ (Promote _ b))) r = do
  --
  x <- freshVariable' y
  --
  let heap' = (x, (r, b)) : heap
  return (subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , r)]))

-- [Small-AppBetaLinear] - Linear beta-redux, because Granule
smallHeapReduxAux defs heap
    (App _ _ _ (Val s _ _ (Abs _ (PVar _ _ _ y) _ a)) b) r = do
  --
  x <- freshVariable' y
  --
  let heap' = (x, (r, b)) : heap
  return (subst (Val s () False (Var () x)) y a, (heap' , ctxtMap (const (TyGrade Nothing 0)) heap, [(x , r)]))

-- [BETA]
smallHeapReduxAux defs heap
   t@(App s a b (Val s' a' b' (Abs a'' p mt e)) e') r = do
      case smallPatternMatch heap e' p of
        Nothing -> do
          -- Cannot match so do a pattern step eval instead
          mres <- smallPatternHeapStep defs r heap e' p
          case mres of
            NoMatch -> noRedux -- cannot do anything
            Match heap' -> return  (e, (heap', [], []))
            Step heap' e'' out ->
              return (App s a b (Val s' a' b' (Abs a'' p mt e)) e'', (heap', out, []))
        Just heap' -> return (e, (heap', [], []))


-- [App Value - constr beta / turns an application into a 'constr' term]
smallHeapReduxAux defs heap (App s a b (Val s' a' b' (Constr a'' id vs)) (Val _ _ _ v)) r | isValue v =
  return (Val s' a' b' (Constr a'' id (vs ++ [v])), (heap, [], []))


-- COMMUNICATION MODELS
smallHeapReduxAux defs heap (App s a b (Val s' a' b' (Var _ (internalName -> "forkLinear'"))) e) r = do

  -- Name/'pointer' for the channel
  v <- freshVariable' (mkId "c")

  -- Make a new channel and put it in the heap
  let chan = Val s' a' b' (Ext () (Chan []))
  let localHeap = [(v, (TyGrade Nothing 1, chan))]

  -- Make chan pointer
  let chanPointer = Val s' a' b' (Ext () (ChanPointer v))

  -- Fork the process
  lift $ fork (App s a b e (Val s' a' b' (Promote a' chanPointer)))

  -- Return
  return (chanPointer, (localHeap ++ heap, [], []))

-- [Small-AppL]
smallHeapReduxAux defs heap (App s a b e1 e2) r | not (isValueExpr e1) = do
  res@(e1', (h, resourceOut, gammaOut)) <- smallHeapReduxAux defs heap e1 r
  return (App s a b e1' e2, (h, resourceOut, gammaOut))

-- [App Value]
smallHeapReduxAux defs heap t@(App s a b e1 e2) r | isValueExpr e1 = do
  case (e1, e2) of
    -- Send case
    (UApp (UVal (UVar (internalName -> "send'"))) chan@(UVal (Ext () (ChanPointer chanPointer))), e) ->
      case lookupAndCutout chanPointer heap of
        Nothing -> noRedux
        Just (heap', (rq, (Val _ _ _ (Ext _ (Chan queue))))) -> do
          -- send on the channel
          let heap'' = (chanPointer, (rq, (Val s () True $ Ext () $ Chan (queue ++ [e])))) : heap'
          return (chan, (heap'', [], []))
        Just _ -> noRedux

    (Val s' a' b' (Var _ (internalName -> "recv")), chan@(UVal (Ext () (ChanPointer chanPointer)))) ->
      case lookupAndCutout chanPointer heap of
        Nothing -> noRedux

        -- nothing to receive yet
        Just (heap', (rq, (Val _ _ _ (Ext _ (Chan []))))) -> noRedux

        Just (heap', (rq, (Val ss () bb (Ext () (Chan (e:es)))))) -> do
          let localHeap = [(chanPointer, (rq, Val ss () bb (Ext () (Chan es))))]
          return (App s a b (App s a b (Val s a b (Constr a (mkId ",") [])) e) chan, (heap' ++ localHeap, [], []))

        Just _ -> noRedux

    _ -> do
      (e2', env) <- smallHeapReduxAux defs heap e2 r
      return (App s a b e1 e2', env)

-- [Case-Sum-Beta] Matches Left-Right patterns for either
smallHeapReduxAux defs heap
   (Case s a b (App _ _ _ (Val _ _ _ (Constr _ (internalName -> constr) [])) e)
        [(PConstr _ _ _ (internalName -> "Left") [PVar _ _ _ varl], el)
        ,(PConstr _ _ _ (internalName -> "Right") [PVar _ _ _ varr], er)]) r = do

    -- fresh variable
    x <- freshVariable' (if constr == "Left" then varl else varr)
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
    return (eFinal, (heap' , resourceOut, embeddedCtxt))

-- [Case-Product-Beta]
smallHeapReduxAux defs heap
  (Case s a b (App _ _ _ (App _ _ _ (Val _ _ _ (Constr _ (internalName -> ",") [])) e1) e2)
        [(PConstr _ _ _ (internalName -> ",") [PVar _ _ _ var1, PVar _ _ _ var2], e)]) r = do
  -- fresh variables
  x1 <- freshVariable' var1
  x2 <- freshVariable' var2
  --
  let heap' = (x1, (r, e1)) : (x2, (r, e2)) : heap
  --
  let resourceOut = ctxtMap (const (TyGrade Nothing 0)) heap
  let embeddedCtxt = [(x1 , r), (x2, r)]
  -- Expression is e1 or e2 (with x replaying varl or varr)
  return (subst (Val s () False (Var () x1)) var1 (subst (Val s () False (Var () x2)) var2 e), (heap' , resourceOut, embeddedCtxt))

-- [Case-Box-Beta]
smallHeapReduxAux defs heap
  (Case s a b (Val _ _ _ (Promote _ e)) [(PBox _ _ _ (PVar _ _ _ var), e')]) r = do
  -- fresh variables
  x <- freshVariable' var
  --
  let heap' = (x, (r, e)) : heap
  --
  let resourceOut = ctxtMap (const (TyGrade Nothing 0)) heap
  let embeddedCtxt = [(x, r)]
  -- Expression is e1 or e2 (with x replaying varl or varr)
  return (subst (Val s () False (Var () x)) var e', (heap' , resourceOut, embeddedCtxt))

-- [Case-cong]
smallHeapReduxAux defs heap (Case s a b e ps) r = do
  res@(e', (h, resourceOut, gammaOut)) <- smallHeapReduxAux defs heap e r
  return (Case s a b e' ps, (h, resourceOut, gammaOut))

smallHeapReduxAux defs heap (Val s a b (Promote a' e)) r = do
  (e', env) <- smallHeapReduxAux defs heap e r
  return (e', env)

-- -- [Value]
-- smallHeapRedux defs heap (App _ _ _ (Val s' a' b' (Constr a'' id es)) e) r =
--   return $ (Val s' a' b' (Constr a'' id (es ++ [e])), (heap, [], []))

-- Catch all
smallHeapReduxAux defs heap t r = noRedux

noRedux :: Monad m => MaybeT m a
noRedux = MaybeT $ return Nothing

-- Used when no reduction can be done on the 'main' expression and instead
-- we should try to reduce a process
smallHeapReduxPar :: (?globals :: Globals)
              => Ctxt (Def Symbolic ())
              -> Heap
              -> Expr Symbolic ()
              -> Grade
              -> State ([Process], Integer) (Expr Symbolic (), (Heap, Ctxt Grade, Ctxt Grade))
smallHeapReduxPar defs heap e r = do
  -- No reduction can be done on `e` so let's try a concurrent process
  (processes, n) <- get
  case processes of
    [] -> -- No processes so just return this one
      return (e, (heap, [], []))
    (p:processes') -> do
      -- Remove this process for now
      put (processes', n)
      -- Try to reduce it (using the version which won't do parallel reduction itself)
      res <- runMaybeT $ smallHeapReduxAux defs heap p r
      case res of
        Just (p', env) -> do
          -- Get the current state and add this process to the back
          (processes'', m) <- get
          put (processes'' ++ [p'], m)
          --
          return (e, env)
        Nothing ->
          return (e, (heap, [], []))

-- Corresponds to H |- t |> p ~> H'
smallPatternMatch :: Heap ->  Expr Symbolic () -> Pattern () -> Maybe Heap
smallPatternMatch h t (PVar _ _ _ v) = Just ((v, (undefined, t)) : h)

smallPatternMatch h t (PWild _ _ _) = Just h

smallPatternMatch h (Val _ _ _ (Promote _ t)) (PBox _ _ _ p) =
  smallPatternMatch h t p

smallPatternMatch h (Val s a b (Constr _ _ vs)) (PConstr _ _ _ id ps) =
  foldrM (\(vi, pi) -> \hi -> smallPatternMatch hi (Val s a b vi) pi) h (zip vs ps)

smallPatternMatch _ _ _ = Nothing

data PatternResult =
    Match Heap
  | NoMatch
  | Step Heap (Expr Symbolic ()) (Ctxt Grade)

-- Corresponds to H |- t |> p ~> H' |- t' |> p' | Delta
smallPatternHeapStep :: (?globals :: Globals)
  => Ctxt (Def Symbolic ()) -> Grade
  -> Heap
  -> Expr Symbolic ()
  -> Pattern ()
  -> MaybeT (State ([Process], Integer)) PatternResult

smallPatternHeapStep defs r h e p@(PConstr _ _ _ c ps) =
  patternZip defs r h e c (toSnocList ps)

smallPatternHeapStep defs r heap e p = do
  case smallPatternMatch heap e p of
    Nothing -> do
      (e', (heap', out, _)) <- smallHeapReduxAux defs heap e r
      return $ Step heap' e' out

    Just heap' -> return $ Match heap'


{- }
smallPatternHeapStep defs r h e@(Val s a b (Constr _ _ vs)) p@(PConstr _ _ _ c ps) = do
  case partitionPatternReuslt $ map (\(vi, pi) -> smallPatternHeapStep defs r h (Val s a b vi) pi) (zip vs ps) of
    Nothing -> return NoMath
    Just (_, )
  case yes of
    [] -> undefined
    _ ->
      case notYets of

        ((vk, pk) : vps) -> do
          smallHeapRedux defs heap
        _ -> return Nothing

-- [CaseStepCon]
smallPatternHeapStep defs r h t p@(PConstr _ _ _ c ps) = do
  (t', (heap, out, _) <- smallHeapRedux defs heap t r
  return (Step heap t' out)


-- smallPatternHeapStep defs r h t p@(PConstr _ _ _ c ps) = do
--   (t', (heap', resourceOut, _)) <- smallHeapRedux defs h t r
--   return (heap', t', p, resourceOut)
-}

-- smallPatternHeapStep defs r h t p = return NoMatch

leftMostIsConstr :: Expr a b -> Bool
leftMostIsConstr (App _ _ _ (Val _ _ _ (Constr _ x _)) _) = True
leftMostIsConstr (App _ _ _ e1 e2) = leftMostIsConstr e1
leftMostIsConstr _ = False

toSnocList :: [a] -> SnocList a
toSnocList xs = toSnocList' xs Nil
  where
    toSnocList' :: [a] -> (SnocList a -> SnocList a)
    toSnocList' []  = id
    toSnocList' (x : xs) = (toSnocList' xs) . (\z -> Snoc z x)


fromSnocList :: SnocList a -> [a]
fromSnocList Nil = []
fromSnocList (Snoc xs x) = fromSnocList xs ++ [x]

data SnocList a = Snoc (SnocList a) a | Nil

patternZip :: (?globals :: Globals) =>
     Ctxt (Def Symbolic ())
  -> Grade
  -> Heap
  -> Expr Symbolic ()
  -> Id
  -> SnocList (Pattern ())
  -> MaybeT (State ([Process], Integer)) PatternResult

-- Constructor match
patternZip defs r heap (Val s a b (Constr _ id' [])) id Nil | id == id' =
  return $ Match heap

-- Applied constructor match
patternZip defs r heap (Val s a b (Constr s' id' (v:vs))) id ps | id == id' =
  case fromSnocList ps of
    (p' : ps') ->
      -- try the first var against the first pattern
      case smallPatternMatch heap (Val s a b v) p' of
        Nothing -> return $ NoMatch
        -- success to recurse
        Just heap' ->
          patternZip defs r heap' (Val s a b (Constr s' id' vs)) id (toSnocList ps')
    [] -> error "Bug"

patternZip defs r heap (App s a b e1 e2) id (Snoc ps p) | leftMostIsConstr e1 = do
  res <- patternZip defs r heap e1 id ps
  case res of
    NoMatch -> return NoMatch
    Match heap' -> do
      -- everything else matches so now try to step here
      res <- smallPatternHeapStep defs r heap' e2 p
      case res of
        Step heap'' e2' out -> return $ Step heap'' (App s a b e1 e2') out
        other               -> return other
    Step heap' e1' out -> return $ Step heap' (App s a b e1' e2) out

patternZip defs r heap e id ps = do
  (e', (heap', out, _)) <- smallHeapReduxAux defs heap e r
  return $ Step heap' e' out

{-
patternZip ::
     Ctxt (Def Symbolic ())
  -> Grade
  -> Heap
  -> Id
  -> [Expr Symbolic ()] -> [Pattern Symbolic ()] -> Expr Symbolic () -> State ([Process], Integer) PatternResult
patternZip defs r h id (e:es) (p:ps) acc = do
  case smallPatternHeapStep defs r h e p of
    NoMatch   -> return NoMatch
    (Match h') -> do
      res <- patternZip defs r h' es ps
      case res of
        NoMatch -> return NoMatch
        Match h -> return $ Match h
        (Step h' es' out) -> return $ Step h' (unreassociatedNestedAppConstr' es') out
    (Step h e' out) -> return $ Step h (unreassociatedNestedAppConstr id (e':es))



partitionPatternReuslt :: [PatternResult] -> Maybe ([Heap], [(Heap, Expr Symbolic (), Ctxt Grade)])
partitionPatternReuslt (NoMatch:_) = Nothing

partitionPatternReuslt ((Match h):rs) = do
  (as, bs) <- partitionPatternReuslt rs
  return (h : as, bs)

partitionPatternReuslt ((Step h e out):rs) = do
  (as, bs) <- partitionByMaybe rs
  return (as, (h, e, out) : bs)
-}

-- Things that cannot be reduced further by this model
isValueExpr :: Expr a b -> Bool
isValueExpr (Val _ _ _ v) = isValue v
isValueExpr _ = False

isValue :: Value a b -> Bool
isValue Promote{} = True -- TODO: PROBABLY NOT
isValue (Constr _ _ vs) = all isValue vs
isValue NumInt{} = True
isValue NumFloat{} = True
isValue CharLiteral{} = True
isValue StringLiteral{} = True
isValue Ext{} = True
isValue (Var _ id) =
  -- some primitives count as values
  case internalName id of
    "recv" -> True
    "send" -> True
    "forkLinear" -> True
    "forkLinear'" -> True
    _ -> False
isValue _ = False

freshVariable' :: Id -> MaybeT (State ([Process], Integer)) Id 
freshVariable' = lift . freshVariable

freshVariable :: Id -> State ([Process], Integer) Id
freshVariable x = do
  (ps, st) <- get
  let x' = mkId $ (internalName x) ++ "." ++ show st
  put $ (ps, st+1)
  return x'

toHeap :: Pattern a -> Heap
toHeap (PVar _ _ _ v)       = [(v, (TyGrade Nothing 1, (Val nullSpanNoFile () False (Ext () (Symbolic v)))))]
toHeap (PBox _ _ _ p)       = toHeap p
toHeap (PConstr _ _ _ _ ps) = concatMap toHeap ps
toHeap _ = []

fork :: Expr Symbolic () -> State ([Process], Integer) ()
fork e = do
  (ps, n) <- get
  put (e : ps, n)