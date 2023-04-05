{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-unused-imports #-}
{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
module Language.Granule.Synthesis.Synth where

import Data.List (sortBy,nub, nubBy, intercalate, find)

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
-- import Control.Monad.Logic
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span

-- import Data.List.NonEmpty (NonEmpty(..))

import Language.Granule.Context

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Coeffects(getGradeFromArrow)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables
import Language.Granule.Synthesis.Builders
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Contexts
import Language.Granule.Synthesis.Common


import Data.Either (lefts, rights, fromRight)
import Control.Monad.State.Strict

-- import qualified Control.Monad.State.Strict as State (get)
import qualified System.Clock as Clock
-- import qualified Control.Monad.Memo as Memo
import qualified System.Timeout
import qualified Data.List.Ordered as Ordered

import Language.Granule.Utils
import Data.Maybe (fromMaybe)
-- import Control.Arrow (second)
-- import Control.Monad.Omega
import System.Clock (TimeSpec)

-- import Control.Monad.Except
-- import Control.Monad.Logic
import Data.Ord
import Debug.Trace
import Language.Granule.Syntax.Def
import Control.Exception (SomeException)
import Language.Granule.Synthesis.RewriteHoles (holeRefactor)

------------------------------

-- Additional semiring-dependent constraints for additive resource management.
-- If we are in additive mode, we can finish early if such a constraint is not
-- satisfiable:
--
-- ∀x,y . x ⊑︎ y => xRy
--
increasingConstraints :: (?globals :: Globals) => Ctxt SAssumption -> Ctxt SAssumption -> Synthesiser ()
increasingConstraints gamma delta = increasingConstraints' gamma delta False
  where
    increasingConstraints' [] delta addedConstraints = do
      res <- if addedConstraints then solve else return True
      boolToSynthesiser res ()
    increasingConstraints' (gVar@(name, SVar (Discharged _ grade) _ _):gamma) delta addedConstraints =
      case lookup name delta of
        Just (SVar (Discharged _ grade') _ _) -> do
          (kind, _, _) <- conv $ synthKind ns grade
          addIncreasingConstraint kind grade grade'
          increasingConstraints' gamma delta True
        _ -> increasingConstraints' gamma delta addedConstraints


addIncreasingConstraint :: Kind -> Type -> Type -> Synthesiser ()
addIncreasingConstraint k@(isInterval -> Just t) gradeIn gradeOut = do
  st <- conv get
  var <- freshIdentifier
  conv $ existentialTopLevel var k
  liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
  liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
  -- modifyPred st $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

addIncreasingConstraint k@(TyCon con) gradeIn gradeOut  =
  case internalName con of

    -- Natural Numbers: R = {(x, y) | ∃z. x + z ⊑ y}
    "Nat" -> do
      st <- conv get
      var <- freshIdentifier
      conv $ existentialTopLevel var k
      liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
      liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
      -- modifyPred st $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

    -- Linear/Non Linear: R = {(x, y) | }
    "LNL" -> do
      st <- conv get
      var <- freshIdentifier
      conv $ existentialTopLevel var k
      liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
      liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
      -- modifyPred st $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

    -- TBD
    "Level" -> return ()
    "Borrowing" -> return ()
    "OOZ" -> return ()
addIncreasingConstraint _ _ _ = return ()


noneWithMaxReached :: (?globals :: Globals) => Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
noneWithMaxReached = do
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
                  state {
                    maxReached = True
                    })
  none




markRecursiveType :: Id -> Type -> Bool
markRecursiveType tyCon dataTy = markRecursiveType' tyCon dataTy False
  where
    markRecursiveType' tyCon (FunTy _ _ t1 t2) onLeft = do
      case markRecursiveType' tyCon t1 True of
        True -> True
        False -> markRecursiveType' tyCon t2 onLeft
    markRecursiveType' tyCon (TyApp t1 t2) True = do
      case markRecursiveType' tyCon t1 True of
        True -> True
        False -> markRecursiveType' tyCon t2 True
    markRecursiveType' tyCon (TyCon tyCon') True = tyCon == tyCon'
    markRecursiveType' _ _ _ = False

-- Run from the checker
synthesiseProgram :: (?globals :: Globals)
           => Maybe Hints
           -> Int -- index
           -> Ctxt TypeScheme  -- Unrestricted Defs
           -> Ctxt (TypeScheme, Type) -- Restricted Defs
           -> Id
           -> Ctxt Assumption    -- (unfocused) free variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO ([Expr () ()], Maybe Measurement)
synthesiseProgram hints index unrComps rComps defId ctxt goalTy checkerState = do

  start <- liftIO $ Clock.getTime Clock.Monotonic

  let (timeoutLim, index, gradeOnRule, resourceScheme) =
         case hints of
            Just hints' -> ( case (hTimeout hints', hNoTimeout hints') of
                                  (_, True) -> -1
                                  (Just lim, _) -> lim * 1000,
                            index + (fromMaybe 0 $ hIndex hints'),
                            hGradeOnRule hints' || fromMaybe False (globalsGradeOnRule ?globals),
                            let mode = if (hPruning hints' || alternateSynthesisMode) then Pruning else NonPruning
                            in
                            if (hSubtractive hints' || subtractiveSynthesisMode) then Subtractive else Additive mode
                          )
            Nothing ->    ( -1,
                            index,
                            fromMaybe False (globalsGradeOnRule ?globals),
                            let mode = if alternateSynthesisMode then Pruning else NonPruning
                            in
                            if subtractiveSynthesisMode then Subtractive else Additive mode)

  let gamma = map (\(v, a)  -> (v, (SVar a $ Just $ NonDecreasing 0 ))) ctxt ++
              map (\(v, (Forall _ _ _ ty, grade)) -> (v, (SVar (Discharged ty grade) $ Just $ NonDecreasing 0))) rComps
  let initialGrade = if gradeOnRule then Just (TyGrade Nothing 1)  else Nothing

  let initialState = SynthesisData {
                         smtCallsCount= 0
                      ,  smtTime= 0
                      ,  proveTime= 0
                      ,  theoremSizeTotal= 0
                      ,  paths = 0
                      ,  startTime=start
                      ,  constructors=[]
                      ,  currDef = [defId]
                      ,  maxReached = False
                      ,  attempts = 0
                      }

  let (hintELim, hintILim) = (1, 1) -- case (hasElimHint hints, hasIntroHint hints) of
  --           (Just e, Just i)   -> (e, i)
  --           (Just e, Nothing)  -> (e, 1)
  --           (Nothing, Just i)  -> (1, i)
  --           (Nothing, Nothing) -> (1, 1)

  let timeOutLimit = if interactiveDebugging then maxBound :: Int else timeoutLim
  result <-
    liftIO $ System.Timeout.timeout timeOutLimit $ loop resourceScheme (hintELim, hintILim) index unrComps initialGrade gamma initialState
  fin <- case result of
    Just (synthResults, aggregate) ->  do
      let results = nub $ map fst3 $ rights (map fst synthResults)

      -- Force eval of first result (if it exists) to avoid any laziness when benchmarking
      () <- when benchmarking $ unless (null results) (return $ seq (show $ head results) ())
  -- %%
      end    <- liftIO $ Clock.getTime Clock.Monotonic

      debugM "mode used: " (show resourceScheme)
      debugM "results: " (pretty results)
      case results of
      -- Nothing synthed, so create a blank hole instead
        []    -> do
          debugM "Synthesiser" $ "No programs synthesised for " <> pretty goalTy
          printInfo $ "No programs synthesised"
        _ ->
          case last results of
            t -> do
              debugM "Synthesiser" $ "Synthesised: " <> pretty t
              printSuccess "Synthesised"

      -- <benchmarking-output>
      when benchmarking $
        if benchmarkingRawData then
          putStrLn $ "Measurement "
            <> "{ smtCalls = " <> show (smtCallsCount aggregate)
            <> ", synthTime = " <> show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
            <> ", proverTime = " <> show (proveTime aggregate)
            <> ", solverTime = " <> show (Language.Granule.Synthesis.Monad.smtTime aggregate)
            <> ", meanTheoremSize = " <> show (if smtCallsCount aggregate == 0 then 0 else fromInteger (theoremSizeTotal aggregate) / fromInteger (smtCallsCount aggregate))
            <> ", success = " <> (if null results then "False" else "True")
            <> ", timeout = False"
            <> ", pathsExplored = " <> show (paths aggregate)
            <> " } "
        else do
          -- Output benchmarking info
          putStrLn "-------------------------------------------------"
          putStrLn $ "Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty expr; _ -> "NO SYNTHESIS")
          putStrLn $ "-------- Synthesiser benchmarking data (" ++ show resourceScheme ++ ") -------"
          putStrLn $ "Total smtCalls     = " ++ show (smtCallsCount aggregate)
          putStrLn $ "Total smtTime    (ms) = "  ++ show (Language.Granule.Synthesis.Monad.smtTime aggregate)
          putStrLn $ "Total proverTime (ms) = "  ++ show (proveTime aggregate)
          putStrLn $ "Total synth time (ms) = "  ++ show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
          putStrLn $ "Mean theoremSize   = " ++ show ((if smtCallsCount aggregate == 0 then 0 else fromInteger $ theoremSizeTotal aggregate) / fromInteger (smtCallsCount aggregate))
      -- </benchmarking-output>
      return (map unannotateExpr results)
    _ -> do
      end    <- liftIO $ Clock.getTime Clock.Monotonic
      printInfo $ "No programs synthesised - Timeout after: " <> (show timeoutLim  <> "ms")
      return []
  return (fin, Nothing)

  where

      loop resourceScheme (elimMax, introMax) index defs grade gamma agg = do

--      Diagonal search
        -- let diagonal = runOmega $ liftM2 (,) (each [0..elimMax]) (each [0..introMax])

--      Rectilinear search
        -- let norm (x,y) = sqrt (fromIntegral x^2+fromIntegral y^2)
        -- let mergeByNorm = Ordered.mergeAllBy (comparing norm)
        -- let rectSwap = mergeByNorm (map mergeByNorm [[[(x,y) | x <- [0..elimMax]] | y <- [0..introMax]]])

        -- let lims = rectSwap
        undefined



        -- pRes <- do undefined -- foldM (\acc (elim, intro) ->
        --   case acc of
        --     (Just res, agg') -> return (Just res, agg')
        --     (Nothing, agg')  -> do
        --       putStrLn $  "elim: " <> (show elim) <> " intro: " <> (show intro)
        --       let synRes = synthesise resourceScheme gamma (Focused []) (Depth elim 0 intro) grade (Goal goalTy $ Just NonDecreasing)
        --       (res, agg'') <- runStateT (runSynthesiser index synRes checkerState) (resetState agg')
        --       if (not $ solved res) && (depthReached agg'') then return (Nothing, agg'') else return (Just res, agg'')
        --   ) (Nothing, agg) lims
        -- case pRes of
        --   (Just finRes, finAgg) -> do
        --     return (finRes, finAgg)
        --   (Nothing, finAgg) -> loop resourceScheme (elimMax, introMax) index defs grade gamma finAgg


      -- solved res = case res of ((Right (expr, _, _), _):_) -> True ; _ -> False
      -- resetState = undefined
      -- resetState st = st { depthReached = False }



      -- eval takes an unnanotaed AST, so we need to strip out annotations in order to stitch our synthed expr back into
      -- the original AST. Why do we not synthesise unannotated exprs directly? It's possible we may want to use the type
      -- info in the future.
      unannotateExpr :: Expr () Type -> Expr () ()
      unannotateExpr (App s a rf e1 e2)             = App s () rf (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (AppTy s a rf e1 t)            = AppTy s () rf (unannotateExpr e1) t
      unannotateExpr (Binop s a b op e1 e2)         = Binop s () b op (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (LetDiamond s a b ps mt e1 e2) = LetDiamond s () b (unannotatePat ps) mt (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (TryCatch s a b e p mt e1 e2)  = TryCatch s () b (unannotateExpr e) (unannotatePat p) mt (unannotateExpr e1)  $ unannotateExpr e2
      unannotateExpr (Val s a b val)                = Val s () b (unannotateVal val)
      unannotateExpr (Case s a b expr pats)         = Case s () b (unannotateExpr expr) $ map (\(p, e) -> (unannotatePat p, unannotateExpr e)) pats
      unannotateExpr (Hole s a b ids hints)         = Hole s () b ids hints


      unannotateVal :: Value () Type -> Value () ()
      unannotateVal (Abs a p mt e)        = Abs () (unannotatePat p) mt $ unannotateExpr e
      unannotateVal (Promote a e)         = Promote () $ unannotateExpr e
      unannotateVal (Pure a e)            = Pure () $ unannotateExpr e
      unannotateVal (Nec a e)             = Nec () $ unannotateExpr e
      unannotateVal (Constr a ident vals) = Constr () ident $ map unannotateVal vals
      unannotateVal (Var a idv)           = Var () idv
      unannotateVal (Ext a ev)            = Ext () ev
      unannotateVal (NumInt n)            = NumInt n
      unannotateVal (NumFloat n)          = NumFloat n
      unannotateVal (CharLiteral c)       = CharLiteral c
      unannotateVal (StringLiteral s)     = StringLiteral s


      unannotatePat :: Pattern Type -> Pattern ()
      unannotatePat (PVar s a rf nm)         = PVar s () rf nm
      unannotatePat (PWild s a rf)           = PWild s () rf
      unannotatePat (PBox s a rf p)          = PBox s () rf $ unannotatePat p
      unannotatePat (PInt s a rf int)        = PInt s () rf int
      unannotatePat (PFloat s a rf doub)     = PFloat s () rf doub
      unannotatePat (PConstr s a rf nm pats) = PConstr s () rf nm $ map unannotatePat pats






elapsedTime :: TimeSpec -> TimeSpec -> Integer
elapsedTime start end = round $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)





synthesiseGradedBase :: (?globals :: Globals)
  => AST () ()
  -> CheckerError
  -> Maybe (Spec () ())
  -> ((?globals :: Globals) => AST () () -> IO Bool)
  -> Maybe Hints
  -> Int
  -> Ctxt TypeScheme  -- Unrestricted Defs
  -> Ctxt (TypeScheme, Type) -- Restricted Defs
  -> Id
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption    -- (unfocused) free variables
  -> TypeScheme           -- type from which to synthesise
  -> CheckerState
  -> IO ([(Expr () (), RuleInfo)], Maybe Measurement)
synthesiseGradedBase ast hole spec eval hints index unrestricted restricted currentDef constructors ctxt (Forall _ _ constraints goalTy) cs = do


  -- Start timing and initialise state
  start <- liftIO $ Clock.getTime Clock.Monotonic
  let synthState = SynthesisData {
                         smtCallsCount= 0
                      ,  smtTime= 0
                      ,  proveTime = 0
                      ,  theoremSizeTotal= 0
                      ,  paths = 0
                      ,  startTime=start
                      ,  constructors=[]
                      ,  currDef = [currentDef]
                      ,  maxReached = False
                      ,  attempts = 0
                      }

  constructorsWithRecLabels <- mapM (\(tyId, dataCons) ->
                          do
                            hasRecCon <- foldM (\a (dataConName, (Forall _ _ _ dataTy, _)) ->
                              (if a then return True else return $ markRecursiveType tyId dataTy)
                              ) False dataCons
                            return (tyId, (dataCons, hasRecCon))) constructors


  -- Initialise input context with
  -- local synthesis context
  let gamma = map (\(v, a)  -> (v, SVar a (Just $ NonDecreasing 0) 0)) ctxt ++
  -- restricted definition given as hints
              
  -- restricted definition given as hints
              map (\(v, (tySch, grade)) -> (v, SDef tySch (Just grade) 0)) restricted ++
  -- unrestricted definitions given as hints
              map (\(v, tySch) -> (v, SDef tySch Nothing 0)) unrestricted

  -- Add constraints from type scheme and from checker so far as implication
  (_, cs') <- runChecker cs $ do
    preds <- mapM (compileTypeConstraintToConstraint ns) constraints
    modify (\s ->
       case predicateStack s of
        -- Take implication context off the stack from the incoming checker if there is one
        (_:implContext:_) ->
           s { predicateContext = ImplConsequent [] (Conj $ implContext : lefts preds) Top }
        _ -> s { predicateContext = ImplConsequent [] (Conj $ lefts preds) Top })

  let norm (x,y) = sqrt (fromIntegral x^2+fromIntegral y^2)
  let mergeByNorm = Ordered.mergeAllBy (comparing norm)
  let lims = mergeByNorm (map mergeByNorm [[[(x,y) | x <- [0..10]] | y <- [0..10]]])
  let sParamList = map (\(elim,intro) -> defaultSearchParams { matchMax = elim, introMax = intro }) lims

  let synRes = synLoop ast hole spec eval constructorsWithRecLabels index gamma [] goalTy sParamList
  (res, agg) <- runStateT (runSynthesiser index synRes cs') synthState

  let programs = nubBy (\(expr1, _) (expr2, _) -> expr1 == expr2) $ rights (map fst res)
  traceM $ "programs: "  <> (pretty $ map fst programs)
  end    <- liftIO $ Clock.getTime Clock.Monotonic
        -- <benchmarking-output>
  if benchmarking then
    if benchmarkingRawData then
      let measurement = Measurement
                        { smtCalls = smtCallsCount agg
                        , synthTime = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)
                        , proverTime = proveTime agg
                        , solverTime = Language.Granule.Synthesis.Monad.smtTime agg
                        , meanTheoremSize = if smtCallsCount agg == 0 then 0 else fromInteger (theoremSizeTotal agg) / fromInteger (smtCallsCount agg)
                        , success = if null programs then False else True
                        , timeout = False
                        , pathsExplored = paths agg
                        } in
                return (programs, Just measurement)
          else do
            -- Output benchmarking info
            putStrLn "-------------------------------------------------"
            putStrLn $ "Result = " ++ (case res of ((Right expr, _):_) -> pretty expr; _ -> "NO SYNTHESIS")
            putStrLn $ "-------- Synthesiser benchmarking data (" ++ "Additive NonPruning" ++  ") -------"
            putStrLn $ "Total smtCalls     = " ++ show (smtCallsCount agg)
            putStrLn $ "Total smtTime    (ms) = "  ++ show (Language.Granule.Synthesis.Monad.smtTime agg)
            putStrLn $ "Total proverTime (ms) = "  ++ show (proveTime agg)
            putStrLn $ "Total synth time (ms) = "  ++ show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
            putStrLn $ "Mean theoremSize   = " ++ show ((if smtCallsCount agg == 0 then 0 else fromInteger $ theoremSizeTotal agg) / fromInteger (smtCallsCount agg))
            return (programs, Nothing)
        else
          return (programs, Nothing)





runExamples :: (?globals :: Globals)
            => ((?globals :: Globals) => AST () () -> IO Bool)
            -> AST () ()
            -> [Example () ()]
            -> Id
            -> IO Bool
runExamples eval last@(AST decls defs imports hidden mod) examples defId = do
  let exampleMainExprs =
        map (\(Example input output) -> makeEquality input output) examples
    -- remove the existing main function (should probably keep the main function so we can stitch it back in after)

  let defsWithoutMain = filter (\(Def _ mIdent _ _ _ _) -> mIdent /= mkId entryPoint) defs

  let foundBoolDecl = find (\(DataDecl _ dIdent _ _ _) ->  dIdent == mkId "Bool") decls
  let declsWithBool = case foundBoolDecl of
                        Just decl -> decls
                        Nothing -> boolDecl : decls

  let exampleMainExprsCombined = foldr (\mainExpr acc -> case acc of Just acc' -> Just $ makeAnd mainExpr acc' ; Nothing -> Just mainExpr) Nothing exampleMainExprs
  case exampleMainExprsCombined of
    Nothing -> error "Could not construct main definition for example AST!"
    Just exampleMainExprsCombined' -> do
      -- exmapleMainDef:
      --    (&&') : Bool -> Bool [0..1] -> Bool
      --    (&&') True [y] = y;
      --    (&&') False [_] = False
      --
      --    main : IO ()
      --    main = (example_in_1 == example_out_1) (&&') ... (&&') (example_in_n == example_out_n)
      let exampleMainDef = Def nullSpanNoFile (mkId entryPoint) False Nothing
                              (EquationList nullSpanNoFile (mkId entryPoint) False
                                [(Equation nullSpanNoFile (mkId entryPoint) () False [] exampleMainExprsCombined')]) (Forall nullSpanNoFile [] [] (TyInt 0))
      let astWithExampleMain = AST declsWithBool (defsWithoutMain ++ [exampleMainDef]) imports hidden mod
      eval astWithExampleMain

  where
    boolDecl :: DataDecl
    boolDecl =
      DataDecl nullSpanNoFile (mkId "Bool") [] Nothing
        [ DataConstrNonIndexed nullSpanNoFile (mkId "True") []
        , DataConstrNonIndexed nullSpanNoFile (mkId "False") [] ]



synLoop :: (?globals :: Globals)
        => AST () ()
        -> CheckerError
        -> Maybe (Spec () ())
        -> ((?globals :: Globals) => AST () () -> IO Bool)
        -> Ctxt (Ctxt (TypeScheme, Substitution), Bool)
        -> Int
        -> Ctxt SAssumption
        -> Ctxt SAssumption
        -> Type
        -> [SearchParameters]
        -> Synthesiser (Expr () (), RuleInfo)
synLoop ast hole spec eval constrs index gamma omega goal [] = none
synLoop ast hole spec eval constrs index gamma omega goal (sParams:rest) = do
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             constructors = constrs
                  })

  synthState <- getSynthState
  cs <- conv $ get
  (res, _) <- liftIO $ runStateT (runSynthesiser index (gSynthOuter ast hole spec eval sParams gamma omega goal) cs) synthState
  case res of
    (_:_) ->
      case last res of
        (Right (expr, delta, _, _, _, ruleInfo), _) -> return (expr, ruleInfo)
        _ -> none
    _ ->
      synLoop ast hole spec eval constrs index gamma omega goal rest

gSynthOuter :: (?globals :: Globals)
            => AST () ()
            -> CheckerError
            -> Maybe (Spec () ())
            -> ((?globals :: Globals) => AST () () -> IO Bool)
            -> SearchParameters
            -> Ctxt SAssumption
            -> Ctxt SAssumption
            -> Type
            -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
gSynthOuter
  ast
  (HoleMessage sp hgoal hctxt htyVars hVars synthCtxt _)
  spec
  eval
  sParams
  gamma
  omega
  goal = do
  res@(expr, delta, _, _, _, _) <- gSynthInner sParams RightAsync gamma (Focused omega) goal
  consumed <- outerContextConsumed (gamma ++ omega) delta
  if consumed
    then case spec of
      Just (Spec _ _ examples@(_:_) _) -> do
        st <- getSynthState
        let hole = HoleMessage sp hgoal hctxt htyVars hVars synthCtxt [([], expr)]
        let holeCases = concatMap (\h -> map (\(pats, e) -> (errLoc h, zip (getCtxtIds (holeVars h)) pats, e)) (cases h)) [hole]
        let ast' = holeRefactor holeCases ast
        let [def] = currDef st

        success <- liftIO $ runExamples eval ast' examples def

        Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             attempts = attempts st + 1
                })
        case (success, attempts st < toInteger exampleLimit) of
          (True, _) -> return res
          (False, True) -> none
          (False, False) -> error "example lim reached"
      _ -> return res

    else none
gSynthOuter _ _ _ _ _ _ _ _ = none



outerContextConsumed :: (?globals::Globals) => Ctxt SAssumption -> Ctxt SAssumption -> Synthesiser Bool
outerContextConsumed input delta = do
  res <- mapM (\(id, a) -> do
                    case lookup id delta of
                      Just (SVar (Discharged _ gradeUsed) _ _) ->
                        case a of
                          (SVar (Discharged _ gradeSpec) _ _) -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeUsed
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns gradeUsed gradeSpec kind)
                            solve
                          _ -> return False
                      Just (SDef _ (Just gradeUsed) _) ->
                        case a of
                          (SDef _ (Just gradeSpec) _) -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeUsed
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns gradeUsed gradeSpec kind)
                            solve
                          _ -> return False
                      Just (SDef _ Nothing _) -> return True
                      Nothing -> return False
                      ) input
  return $ and res



gSynthInner :: (?globals :: Globals)
  => SearchParameters
  -> FocusPhase
  -> Ctxt SAssumption
  -> FocusedCtxt SAssumption
  -> Type
  -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
gSynthInner sParams focusPhase gamma (Focused omega) goal = do

  case (focusPhase, omega) of
    (RightAsync, _) -> do
      -- let (funs, gamma') = funVars (gamma ++ omega)
      -- varRule gamma' (Focused []) (Focused $ funs) goal
      -- `try`
      absRule sParams RightAsync gamma (Focused omega) goal
      `try`
      transitionToLeftAsync sParams gamma omega goal

    (LeftAsync, _:_) -> do
      unboxRule sParams LeftAsync gamma (Focused []) (Focused omega) goal
      `try`
      caseRule sParams LeftAsync gamma (Focused []) (Focused omega) goal
    -- Focus / shift to Sync phases
    (LeftAsync, []) -> do
      foc sParams goal gamma 

    (RightSync, []) -> do
      boxRule sParams RightSync gamma goal
      `try` 
      constrRule sParams RightSync gamma goal


    (LeftSync, [(_, var)]) ->
      case tyAndGrade var of
        Just (ty, _) -> 
          varRule gamma (Focused []) (Focused omega) goal
          `try`
          appRule sParams LeftSync gamma (Focused []) (Focused omega) goal
        _ -> none

    (LeftSync, _) ->  
        gSynthInner sParams RightAsync gamma (Focused []) goal

  where

    foc sParams goal gamma | not (isAtomic goal) && isRSync goal = do 
        focLeft sParams [] gamma goal
        `try`
        focRight sParams gamma goal
    foc sParams goal gamma =
      focLeft sParams [] gamma goal

    focRight sParams gamma = do 
      gSynthInner sParams RightSync gamma (Focused [])

    focLeft _ _ [] goal = none
    focLeft sParams left (var:right) goal = do 
      -- Try focusing first on var first
      gSynthInner sParams LeftSync (left ++ right) (Focused [var]) goal
      `try`
      -- If that fails pick a different var
      focLeft sParams (var:left) right goal

    transitionToLeftAsync _ _ _ (FunTy{}) = none
    transitionToLeftAsync sParams gamma omega goal = gSynthInner sParams LeftAsync gamma (Focused omega) goal


    -- funVars [] = ([], [])
    -- funVars (v@(_, SVar (Discharged (FunTy{}) _) _ _):vars) = 
    --   let (funVars', rest) = funVars vars in
    --   (v:funVars', rest)
    -- funVars (v:vars) =
    --   let (funVars', rest) = funVars vars in
    --   (funVars', v:rest)







{-

--------------------------------- Var
Γ, x :ᵣ A ⊢ A => x | 0·Γ, x :₁ A

-}
varRule :: (?globals :: Globals)
  => Ctxt SAssumption
  -> FocusedCtxt SAssumption
  -> FocusedCtxt SAssumption
  -> Type
  -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
varRule _ _ (Focused []) _ = none
-- varRule gamma (Focused left) (Focused (var@(name, SVar (Discharged t grade) sInfo) : right)) goal = do
varRule gamma (Focused left) (Focused (var@(name, assumption) : right)) goal = do
    -- let ruleInfo = VarRuleP var goal gamma (left ++ right) Nothing
    -- conv $ modify (\s -> { searchTree = addRuleToSearchTree ruleInfo })
    modifyPath ("var on: " <> (pretty name <> " : " <> pretty assumption) <> ", goal: " <> (pretty goal))
    debugM "varRule, goal is" (pretty goal)
    assumptionTy <- getSAssumptionType assumption
    case assumptionTy of
      (t, funDef, mGrade, mSInfo, tySch, _) -> do
        conv resetAddedConstraintsFlag
        st <- conv get
        debugM "equality in var rule" ("tyVarContext = " ++ pretty (tyVarContext st) ++ "\n" ++ pretty t ++ " = "  ++ pretty goal)
        (success, _, subst) <- conv $ equalTypes ns t goal
        cs <- conv get
        modifyPred $ addPredicateViaConjunction (Conj $ predicateStack cs)
        conv $ modify (\s -> s { predicateStack = []})

        if success then do
          solved <- if addedConstraints cs
                    then solve
                    else return True
          -- now to do check we can actually use it
          if solved then do
            case (funDef, mGrade) of
              (False, Just grade) -> do
                (kind, _, _) <- conv $ synthKind ns grade
                delta <- ctxtMultByCoeffect (TyGrade (Just kind) 0) (left ++ right ++ gamma)
                let singleUse = (name, SVar (Discharged t (TyGrade (Just kind) 1)) mSInfo 0)
                let rInfo = VarRule name assumption goal gamma (left ++ right) (singleUse:delta)
                -- let ruleInfo' = modifyVarRule ruleInfo (singleUse:delta)
                -- conv $ modify (\s -> { searchTree = addRuleToSearchTree ruleInfo' })
                leafExpr (Val ns () False (Var () name), singleUse:delta, subst, isDecr mSInfo, Nothing, rInfo)

              (True, Just grade) -> do
                synSt <- getSynthState
                if not $ name `elem` currDef synSt then do
                  (kind, _, _) <- conv $ synthKind ns grade
                  delta <- ctxtMultByCoeffect (TyGrade (Just kind) 0) (left ++ right ++ gamma)
                  let singleUse = (name, SDef tySch (Just $ TyGrade (Just kind) 1) 0)
                  let rInfo = VarRule name assumption goal gamma (left ++ right) (singleUse:delta)
                  -- let ruleInfo' = modifyVarRule ruleInfo (singleUse:delta)
                  -- conv $ modify (\s -> { searchTree = addRuleToSearchTree ruleInfo' })
                  leafExpr (Val ns () False (Var () name), singleUse:delta, subst, False, Nothing, rInfo)

                else none
              (True, Nothing) -> do
                synSt <- getSynthState
                if not $ name `elem` currDef synSt then do
                  delta <- ctxtMultByCoeffect (TyGrade Nothing 0) (left ++ right ++ gamma)
                  let rInfo = VarRule name assumption goal gamma (left ++ right) (var:delta)
                  -- let ruleInfo' = modifyVarRule ruleInfo (var:delta)
                  -- conv $ modify (\s -> { searchTree = addRuleToSearchTree ruleInfo' })
                  leafExpr (Val ns () False (Var () name), var:delta, subst, False, Nothing, rInfo)

                else none
          else none
        else none
    `try` varRule gamma (Focused (var:left)) (Focused right) goal
-- varRule _ _ _ _ = none


{-

Γ, x :ᵣ A ⊢ B => t | Δ, x :ᵣ A      r ⊑ q
-------------------------------------------- Abs
Γ ⊢ Aʳ → B => λᵣx.t | Δ

-}
absRule :: (?globals :: Globals) => SearchParameters ->  FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
absRule sParams focusPhase gamma (Focused omega) goal@(FunTy name gradeM tyA tyB) = do
  debugM "abs, goal is" (pretty goal)
  modifyPath ("absBranchStart")
  modifyPath ("absRule: "  <> (pretty goal))

  -- Extract the graded arrow, or use generic 1 if there is no grade
  let grade = getGradeFromArrow gradeM

  x <-  useBinderNameOrFreshen name
  st <- getSynthState

  -- predicate on whether we want to focus on the argument type or delay
  let bindToOmega =
      -- argument type must be left async type
          (isLAsync tyA)
      -- if we are a recursive type then check whether we are below max depth
        && ((isRecursiveType tyA (constructors st)) ==> (matchCurrent sParams) <= matchMax sParams)
  let (gamma', omega') = bindToContext (x, SVar (Discharged tyA grade) (Just $ NonDecreasing 0) 0) gamma omega bindToOmega 


  (t, delta, subst, struct, scrutinee, rInfo) <-
     -- Recursive call
    --  withPartialExprAt downExpr
      --  (Val ns () False (Abs () (PVar ns () False x) Nothing hole))
       (gSynthInner sParams focusPhase gamma' (Focused omega') tyB)

  modifyPath ("absBranchEnd")

  cs <- conv get
  (kind, _, _) <- conv $ synthKind nullSpan grade
  case lookupAndCutout x delta of
    Just (delta', SVar (Discharged _ grade_r) _ _) -> do
      modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_r grade kind)
      res <- solve
      let rInfo' = AbsRule focusPhase goal gamma omega (x, SVar (Discharged tyA grade) (Just $ NonDecreasing 0) 0) t rInfo delta' 
      debugM "Path taken: \n" (printSynthesisPath (reverse $ synthesisPath cs) 0)
      boolToSynthesiser res (Val ns () False (Abs () (PVar ns () False x) Nothing t), delta', subst, struct, scrutinee, rInfo')

    Nothing -> do
      modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) grade kind)
      res <- solve
      let rInfo' = AbsRule focusPhase goal gamma omega (x, SVar (Discharged tyA grade) (Just $ NonDecreasing 0) 0) t rInfo delta
      boolToSynthesiser res (Val ns () False (Abs () (PVar ns () False x) Nothing t), delta, subst, struct, scrutinee, rInfo')


absRule _ _ _ _ _ = none


{-

Γ, x :_r1 A^q → B, y :_r2 B ⊢ C => t₁ | Δ₁, x :_s1 A^q → B, y :_s2 B
Γ, x :_r1 A^q → B ⊢ A => t₂ | Δ₂, x :_s3 : A^q → B
----------------------------------------------------------------------------------------------:: app
Γ, x : A → B ⊢ C => [(x t₂) / y] t₁ | (Δ₁ + s2 · q · Δ₂), x :_s2 + s1 + (s2 · q · s3) A^q → B

let x2 = x1 t2 in t1

-}
appRule :: (?globals :: Globals) => SearchParameters -> FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
appRule _ _ _ _ (Focused []) _ = none
appRule sParams focusPhase gamma (Focused left) (Focused (var@(x1, assumption) : right)) goal =
  do
    assumptionTy <- getSAssumptionType assumption
    st <- getSynthState
    case (assumptionTy, scrutCurrent sParams < scrutMax sParams) of
      ((FunTy bName gradeM tyA tyB, funDef, Just grade_r, sInfo, tySch, depth), _) -> do
        if depth < appMax sParams then do 
          let grade_q = getGradeFromArrow gradeM

          let omega = left ++ right
          x2 <- freshIdentifier

          modifyPath ("app on: " <> pretty x1 <> " : " <> pretty assumption <> ", binding: " <> (pretty x2) <> " : " <> (pretty tyB) <> " % " <> (pretty grade_r) <> ", with goal: " <> (pretty goal))

          -- predicate on whether we want to focus on the argument type or delay
          let bindToOmega =
              -- argument type must be left async type
                  (isLAsync tyA)
              -- if we are a recursive type then check whether we are below max depth
                && ((isRecursiveType tyA (constructors st)) ==> (matchCurrent sParams) <= matchMax sParams)
          let (gamma', omega') = bindToContext (x2, SVar (Discharged tyB grade_r) Nothing 0) (gamma ++ [(increaseDepth var)]) omega bindToOmega


          (t1, delta1, subst1, struct1, scrutinee, rInfo1) <-
            -- withPartialExprAt (downExpr >=> rightExpr)
            -- (letExpr ns (PVar ns () False x2) (App ns () False (Val ns () False (Var () x1)) hole) hole)
            (gSynthInner sParams { scrutCurrent = (scrutCurrent sParams) + 1} focusPhase gamma' (Focused omega') goal)
        

          case lookupAndCutout x2 delta1 of
            -- If the bound variable has a zero grade, then we didn't use it in the applicaton
            Just (delta1', SVar (Discharged _ (TyInfix TyOpTimes (TyGrade _ 0) _)) _ _) -> none
            Just (delta1', SVar (Discharged _ s2) _ _) ->
              case lookupAndCutout x1 delta1' of
                Just (delta1Out, varUsed) -> do
                    let s1 = case varUsed of
                          SVar (Discharged _ s1') _ _ -> s1'
                          SDef tySch (Just s1') _   -> s1'
                          SDef tySch Nothing _     -> undefined
                    let isScrutinee = case scrutinee of Just scr -> scr == x2 ; _ -> False

                    modifyPath ("appBranchStart")
                    (t2, delta2, subst2, struct2, _, rInfo2) <- do

                      navigatePartialExpr (upExpr >=> rightExpr)
                      gSynthInner (sParams { scrutCurrent = (scrutCurrent sParams) + 1 }) RightAsync (omega ++ gamma ++ [(increaseDepth var)]) (Focused []) tyA

                    modifyPath ("appBranchEnd")
                    case lookupAndCutout x1 delta2 of
                      Just (delta2', varUsed') -> do
                        let s3 = case varUsed' of
                              SVar (Discharged _ s3') _ _ -> s3'
                              SDef tySch (Just s3') _   -> s3'
                              SDef tySch Nothing _     -> undefined
                        delta2Out <- (s2 `ctxtMultByCoeffect` delta2') >>= (\d2' -> grade_q `ctxtMultByCoeffect` d2')
                        -- s2 + s1 + (s2 * q * s3)
                        let outputGrade = s2 `gPlus` s1 `gPlus` (s2 `gTimes` grade_q `gTimes` s3)
                        if (struct1 || struct2) || notElem x1 (currDef st) then
                          case ctxtAdd delta1Out delta2Out of
                            Just delta3 -> do
                              substOut <- conv $ combineSubstitutions ns subst1 subst2
                              let appExpr = App ns () False (Val ns () False (Var () x1)) t2
                              let assumption' = if funDef
                                  then (x1, SDef tySch (Just outputGrade) 0)
                                  -- TODO: We should be able to return "Just grade_q" instead of "gradeM" here but this fails later on
                                  -- (possibly related to the caseRule)
                                  else (x1, SVar (Discharged (FunTy bName gradeM tyA tyB) outputGrade) sInfo 0)

                              let rInfo' = AppRule focusPhase var goal gamma omega (x2, SVar (Discharged tyB grade_r) Nothing 0) t1 rInfo1 delta1 t2 rInfo2 delta2 (assumption':delta3)
                              return (Language.Granule.Syntax.Expr.subst appExpr x2 t1, assumption':delta3, substOut, struct1 || struct2, if isScrutinee then Nothing else scrutinee, rInfo')
                            _ -> none
                          else none
                      _ -> none
                _ -> none
            _ -> none
        else none
      _ -> none
  `try` appRule sParams focusPhase gamma (Focused (var : left)) (Focused right) goal



{-


Γ ⊢ A => t | Δ
------------------------ :: box
Γ ⊢ □ᵣA => [t] | r · Δ

-}
boxRule :: (?globals :: Globals) => SearchParameters -> FocusPhase -> Ctxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
boxRule sParams focusPhase gamma goal@(Box grade_r goal_inner) = do
  debugM "boxRule, goal is" (pretty goal)
  modifyPath ("box: "  <> (pretty goal))

  (t, delta, subst, struct, scrutinee, rInfo) <-
    -- withPartialExprAt downExpr
    -- (Val ns () False (Promote () hole))
    (gSynthInner sParams focusPhase gamma (Focused []) goal_inner)

  delta' <- ctxtMultByCoeffect grade_r delta
  let boxExpr = Val ns () False (Promote () t)
  let rInfo' = BoxRule focusPhase goal gamma t rInfo delta'
  return (boxExpr, delta', subst, struct, scrutinee, rInfo')
boxRule _ _ _ _ = none


{-

Γ, y :_r·q A, x :_r □q A ⊢ B => t | Δ, y : [A] s1, x :_s2 □q A
∃s3 . s1 ⊑ s3 · q ⊑ r · q
---------------------------------------------------------------- :: unbox
Γ, x :_r □q A ⊢ B => case x of [y] -> t | Δ, x :_s3+s2 □q A

-}
unboxRule :: (?globals :: Globals) => SearchParameters -> FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
unboxRule _ _ _ _ (Focused []) _ = none
unboxRule sParams focusPhase gamma (Focused left) (Focused (var_x@(x, SVar (Discharged (Box grade_q ty) grade_r) sInfo depth):right)) goal = do 
    debugM "unboxRule, goal is" (pretty goal)
    modifyPath ("unbox: "  <> (pretty goal))

    let omega = left ++ right
    y <- freshIdentifier

    st <- getSynthState

    -- predicate on whether we want to focus on the argument type or delay
    let bindToOmega =
      -- argument type must be left async type
           (isLAsync ty)
      -- if we are a recursive type then check whether we are below max depth
         && ((isRecursiveType ty (constructors st)) ==> (matchCurrent sParams + 1) < matchMax sParams)
    let (gamma', omega') = bindToContext (y, SVar (Discharged ty (grade_r `gTimes` grade_q)) Nothing 0) (var_x:gamma) omega bindToOmega

    (t, delta, subst, struct, scrutinee, rInfo) <-
        -- withPartialExprAt downExpr 
        -- (makeUnboxUntyped y (makeVarUntyped x) hole)
        (gSynthInner sParams focusPhase gamma' (Focused omega') goal)

    case lookupAndCutout y delta of
      Just (delta', SVar (Discharged _ grade_s1) _ _) ->
        case lookupAndCutout x delta' of
          Just (delta'', SVar (Discharged _ grade_s2) _ _) -> do
            cs <- conv get

            grade_id_s3 <- freshIdentifier
            let grade_s3 = TyVar grade_id_s3
            (kind, _, _) <- conv $ synthKind nullSpan grade_s1
            conv $ existentialTopLevel grade_id_s3 kind

            -- ∃s3 . s1 ⊑ s3 · q ⊑ r · q
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (grade_s3 `gTimes` grade_q) (grade_r `gTimes` grade_q) kind)
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_s1 (grade_s3 `gTimes` grade_q) kind)

            res <- solve

            let var_x' = (x, SVar (Discharged (Box grade_q ty) (grade_s3 `gPlus` grade_s2)) sInfo 0)

            let rInfo' = UnboxRule focusPhase var_x goal gamma omega (y, SVar (Discharged ty (grade_r `gTimes` grade_q)) Nothing 0) t rInfo (var_x':delta'')
            boolToSynthesiser res (makeUnboxUntyped y (makeVarUntyped x) t, var_x':delta'', subst, struct, scrutinee, rInfo')
          _ -> none
      _ -> none
unboxRule _ _ _ _ _ _ = none



{-

(C: B₁^q₁ → ... → Bₙ^qₙ → K A ∈ D)
Γ ⊢ Bᵢ => tᵢ | Δᵢ
----------------------------------------------------:: constr
Γ ⊢ K A => C t₁ ... tₙ | (q₁ · Δ₁) + ... + (qₙ · Δₙ)

-}
constrRule :: (?globals :: Globals) => SearchParameters -> FocusPhase -> Ctxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
constrRule sParams focusPhase gamma goal = do
  debugM "constrRule, goal is" (pretty goal)
  st <- getSynthState
  case ((introCurrent sParams <= introMax sParams) || not (isRecursiveType goal (constructors st)), isADTorGADT goal) of
    (reachedLim, Just datatypeName) -> do
      synthState <- getSynthState
      let (recDatacons, datacons) = relevantConstructors datatypeName $ constructors synthState
      let datacons' = sortBy compareArity (recDatacons ++ datacons)
      tryDatacons datatypeName [] datacons' goal reachedLim 

    -- (_, Just _) -> noneWithMaxReached
    _ -> none


  where
    tryDatacons dtName _ [] _ _ = none
    tryDatacons dtName right (con@(cName, (tySc@(Forall s bs cs cTy), cSubst)):left) goal underLim =
       do
        modifyPath ("constr, con: "  <> (pretty cName) <> ", goal: " <> (pretty goal))
        result <- checkConstructor tySc goal cSubst
        case result of
          (True, specTy, args, subst, substFromFreshening, predicate) -> do
            modifyPred (addPredicateViaConjunction predicate)
            case (args, underLim) of
              -- Nullary constructor
              ([], _) -> do
                delta <- ctxtMultByCoeffect (TyGrade Nothing 0) gamma
                let rInfo = ConstrRule focusPhase cName goal gamma (Val ns () False (Constr () cName [])) [] delta 
                leafExpr (Val ns () False (Constr () cName []), delta, [], False, Nothing, rInfo)

              -- N-ary constructor
              (args@(_:_), True) -> do
                st <- getSynthState
                let sParams' = if isRecursiveType goal (constructors st)
                               then sParams { introCurrent = (introCurrent sParams) + 1 }
                               else sParams
                (ts, delta, substOut, structs, rInfos) <- synthArgs args subst sParams' 
                let rInfo = ConstrRule focusPhase cName goal gamma (makeConstrUntyped ts cName) rInfos delta 
                leafExpr (makeConstrUntyped ts cName, delta, substOut, False, Nothing, rInfo)
              _ -> none
          _ -> none
      `try` tryDatacons dtName (con:right) left goal underLim


    synthArgs [] _ _ = return ([], [], [], False, [])
    synthArgs ((ty, mGrade_q):args) subst sParams = do
      (ts, deltas, substs, structs, rInfos) <- synthArgs args subst sParams
      ty' <- conv $ substitute subst ty
      modifyPath ("constrBranchStart")
      (t, delta, subst, struct, _, rInfo) <- gSynthInner sParams RightAsync gamma (Focused []) ty'
      modifyPath ("constrBranchEnd")
      delta' <- maybeToSynthesiser $ ctxtAdd deltas delta
      substs' <- conv $ combineSubstitutions ns substs subst
      delta'' <- case mGrade_q of
        Just grade_q -> ctxtMultByCoeffect grade_q delta'
        _ -> return delta'
      return (t:ts, delta'', substs', struct || structs, rInfo:rInfos)


{-

(C: B₁^q₁ → ... → Bₙ^qₙ → K A ∈ D)

Γ, x :ᵣ K A, y₁ⁱ :_(r · q₁) B₁ ... yₙⁱ :_(r · qₙ) Bₙ ⊢ B => tᵢ | Δᵢ, x :_rᵢ K A, y₁ⁱ :_s₁ⁱ B₁ ... yₙⁱ :_sₙⁱ Bₙ

∃s'ⱼⁱ . sⱼⁱ ⊑ s'ⱼⁱ · qⱼⁱ ⊑ r · qⱼⁱ

sᵢ = s'₁ⁱ ⊔ ... ⊔ s'ₙⁱ

--------------------------------------------------------------------------------------------------------:: case (v1)
Γ, x :ᵣ K A ⊢ B => case x of cᵢ y₁ⁱ ... yₙⁱ -> tᵢ | (Δ₁ ⊔ ... ⊔ Δₙ), x :_(r₁ ⊔ ... ⊔ rₙ)+(s₁ ⊔ ... ⊔ sₙ)

i.e., with a goal of type `B` and `x : r K A` in context we want
to case on it, which involves make a case, pattern matching on all
the constructors `C`

-}

-- Output list of pattern->expr pair for the branch
-- output context D
-- substituion Theta
-- grade r
-- grade s
casePatternMatchBranchSynth :: (?globals :: Globals) =>
     SearchParameters
  -> FocusPhase
  -> Ctxt SAssumption                      -- gamma context
  -> Ctxt SAssumption                      -- omega context
  -> (Id, SAssumption)                     -- var being matched on
  -> Id                                    -- name of the type constructor on which we are match
                                           --    (should be consistent with first parameter)
  -> Type                                  -- branch goal type
  -> (Id, (TypeScheme, Substitution))      -- constructor info
  -> Synthesiser
       (Maybe ((Pattern (), Expr () ()), (Ctxt SAssumption, (Substitution, (Coeffect, Maybe Coeffect), (Id, Ctxt SAssumption, Expr () (), Ctxt SAssumption, RuleInfo)))))
casePatternMatchBranchSynth
  sParams
  focusPhase
  gamma
  omega
  var@(x, SVar (Discharged ty grade_r) sInfo depth)
  datatypeName
  goal
  con@(cName, (tySc@(Forall s bs constraints cTy), cSubst)) = do
  -- Debugging

  debugM "case - constructor" (pretty con)
  

  -- Check that we can use a constructor here
  -- uses peekChecker so that we can roll back any state updates
  (result, commitToCheckerState) <- peekCheckerInSynthesis $ checkConstructor tySc ty cSubst

  case result of
    (True, _, args, subst, _, predicate) -> do
      -- commit to updating the checker state from `checkConstructor`
      conv $ commitToCheckerState
      -- New implication
      modifyPred (newImplication [])
      modifyPred (addPredicateViaConjunction predicate)
      modifyPred (fromRight Top . moveToConsequent)

      -- args contains the types and maybe grade for each argument of this constructor

      -- for every argument position of the constructor we need to create a variable
      -- to bind the result:
      (gamma', omega', branchBoundVarsAndGrades) <-
        forallM args (gamma ++ [var], omega, []) (\(gamma, omega, vars) (argTy, mGrade_q) -> do
          -- Three piece of information calculate:

          -- (i) variable name
          var <- freshIdentifier
          -- (ii) grade
          let grade_rq = case mGrade_q of
                            Just grade_q -> grade_r `gTimes` grade_q
                            -- Contains a small optimisation of avoiding a times * 1
                            Nothing      -> grade_r
          -- (iii) type
          argTy' <- conv $ substitute subst argTy
          st <- getSynthState

          -- Create an assumption for the variable and work out which synthesis environment
          -- to insert it into
          let assumption@(_, SVar _ _ _) =
                -- Check if the constructor here is recursive
                if positivePosition datatypeName argTy'
                then (var, SVar (Discharged argTy' grade_rq) (Just $ Decreasing 0) 0)
                else (var, SVar (Discharged argTy' grade_rq) (Just $ NonDecreasing 0) 0)

          -- predicate on whether we want to focus on the argument type or delay
          let bindToOmega =
                 -- argument type must be left async type
                   (isLAsync argTy')
                 -- if we are a recursive type then check whether we are below max depth
                && ((isRecursiveType argTy' (constructors st)) ==> (matchCurrent sParams + 1) < matchMax sParams)

          -- construct focussing contexts
          let (gamma', omega') = bindToContext assumption gamma omega bindToOmega
          return (gamma', omega', (var, (argTy', getGradeFromArrow mGrade_q, grade_rq, sInfo)):vars)
        )

      -- let boundVarsForPrinting = 
      modifyPath ("caseBranchStart")
      modifyPath 
        ("case branch with con: " <> (pretty cName) <> ", binding: " <> 
          (intercalate ", " $ map (\(x, (argTy, _, grade_rq, _)) -> pretty x <> " : " <> pretty argTy <> " % " <> pretty grade_rq) branchBoundVarsAndGrades))
      let (vars, _) = unzip branchBoundVarsAndGrades
      let constrPat = PConstr ns () False cName (map (PVar ns () False) $ reverse vars)

      -- Synthesise the body of the branch which produces output context `delta`

      (t, delta, subst, _, _, rInfo) <-
         gSynthInner sParams { matchCurrent = (matchCurrent sParams) + 1} focusPhase gamma' (Focused omega') goal

      (delta', grade_si) <- forallM delta ([], Nothing) (\(delta', mGrade) dVar@(dName, dAssumption) ->
        case dAssumption of
          SVar (Discharged ty grade_s) dSInfo _ ->
            -- See if this is a variable being bound in the case
            case lookup dName branchBoundVarsAndGrades of
              Just (_, grade_q, grade_rq, _) -> do

                grade_id_s' <- freshIdentifier
                let grade_s' = TyVar grade_id_s'
                (kind, _, _) <- conv $ synthKind ns grade_s
                conv $ existentialTopLevel grade_id_s' kind
                -- ∃s'_ij . s_ij ⊑ s'_ij · q_ij ⊑ r · q_ij
                modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (grade_s' `gTimes` grade_q) grade_rq kind)
                modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_s (grade_s' `gTimes` grade_q) kind)
                modifyPred $ (ExistsHere grade_id_s' kind)

                -- s' \/ ...
                grade_si <- computeJoin (Just kind) (fromMaybe grade_s' mGrade) (grade_s')
                -- now do not include in the result as this is being bound
                return (delta', Just grade_si)
              -- Not a variable bound in the scope
              _ -> do
                return (dVar:delta', mGrade)
          SDef{} -> do
            return (dVar:delta', mGrade)
        )

      -- Concludes the implication
      -- TODO: maybe run solve here per branch
      modifyPred $ moveToNewConjunct
      modifyPath ("caseBranchEnd")

      let branchCtxt = map (\(x, (argTy, _, grade_rq, sInfo)) -> (x, SVar (Discharged argTy grade_rq) sInfo depth)) branchBoundVarsAndGrades

      case lookupAndCutout x delta' of
        (Just (delta'', SVar (Discharged _ grade_r') sInfo _)) -> do
          if null args then do
            (kind, _, _) <- conv $ synthKind ns grade_r
            let branchInfo = (cName, branchCtxt, t, delta'', rInfo)
            return $ Just ((constrPat, t), (delta'', (subst, (grade_r', Just (TyGrade (Just kind) 1)), branchInfo )))
          else do
            let branchInfo = (cName, branchCtxt, t, delta'', rInfo)
            return $ Just ((constrPat, t), (delta'', (subst, (grade_r', grade_si), branchInfo)))

        _ -> error "Granule bug in synthesiser. Please report on GitHub: scrutinee not in the output context"
    _ -> do
      return Nothing

caseRule :: (?globals :: Globals)
   => SearchParameters
   -> FocusPhase
   -> Ctxt SAssumption
   -> FocusedCtxt SAssumption
   -> FocusedCtxt SAssumption
   -> Type
   -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution, Bool, Maybe Id, RuleInfo)
caseRule _ _ _ _ (Focused []) _ = none
caseRule sParams focusPhase gamma (Focused left) (Focused (var@(x, assumption@(SVar (Discharged ty grade_r) sInfo depth)):right)) goal =
  do
    debugM "caseRule, goal is" (pretty goal)
    modifyPath ("case on: " <> (pretty (x, pretty assumption)) <> ", goal: " <> (pretty goal))

    synthState <- getSynthState
    case ((matchCurrent sParams < matchMax sParams) || not (isRecursiveType ty (constructors synthState)), leftmostOfApplication ty) of
      (True, TyCon datatypeName) -> do

        let omega = left ++ right

        cs <- conv get
        -- If the type is polyshaped then add constraint that we incur a usage
        let (recCons, nonRecCons) = relevantConstructors datatypeName (constructors synthState)

        let datacons = sortBy compareArity (recCons ++ nonRecCons)

          -- Process each data constructor
        branchInformation <-
          mapMaybeM (casePatternMatchBranchSynth
                           sParams focusPhase  -- synth configs
                           gamma omega         -- contexts
                           var                 -- var being match on
                           datatypeName
                           goal) datacons

        let (patExprs, contextsAndSubstsGrades) = unzip branchInformation
        let (deltas, substsAndGrades)           = unzip contextsAndSubstsGrades
        let (substs, grades, branchInfos)                    = unzip3 substsAndGrades
        -- TODO: more clear names here
        let (grade_rs, grade_ss)                = unzip grades

        -- join contexts
        delta <- foldM (ctxtMerge (computeJoin Nothing)) (head deltas) (tail deltas)

        -- join grades
        grade_r_out <- foldM (computeJoin Nothing)  (head grade_rs) (tail grade_rs)
        grade_s_out <- foldM (computeJoin' Nothing) (head grade_ss) (tail grade_ss)


        -- join substitutions
        subst <- conv $ combineManySubstitutions ns substs

        grade_final <- case grade_s_out of
                  -- Add the usages of each branch to the usages of x inside each branch
                  Just grade_s_out' -> return $ grade_r_out `gPlus` grade_s_out'
                  -- Not sure when this case should arise, since nullary constrguctors get a 1 grade
                  Nothing -> return grade_r_out
        -- Focussed variable output assumption
        let var_x_out = (x, SVar (Discharged ty grade_final) sInfo 0)

        debugM "synth candidate" (pretty $ makeCaseUntyped x patExprs)
        solved <-
          ifM (conv $ polyShaped ty)
            (do
              (kind, _, _) <- conv $ synthKind ns grade_r
              debugM ("polyShaped for " ++ pretty goal) (pretty grade_r)
              modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 1) (getGradeFromArrow grade_s_out) kind)
              res <- solve
              debugM "solver result" (show res)
              return res)
            solve

        if solved && not (null patExprs)
          then do 

            -- let branchInfos = undefined
            let rInfo = CaseRule focusPhase var goal gamma omega (makeCaseUntyped x patExprs) branchInfos (var_x_out:delta)
            return (makeCaseUntyped x patExprs, var_x_out:delta, subst, False, Just x, rInfo)
          else none
      (False, _) -> noneWithMaxReached
      _ -> none
  -- `try` caseRule sParams focusPhase gamma (Focused (var : left)) (Focused right) goal

caseRule _ _ _ _ _ _ = none

-- Given two grades, returns their join.
-- and where the first input may specify their kind if its already known

-- Note however that this may also generate predicates
-- (and hence lives in the `Synthesis` monad) as some
-- grades do *not* have a join.

computeJoin :: (?globals :: Globals) => Maybe Kind -> Type -> Type -> Synthesiser Type
computeJoin maybeK g1 g2 = do
  k <- case maybeK of
         Nothing -> conv $ do { (k, _, _) <- synthKind ns g1; return k }
         Just k  -> return k
  upperBoundGradeVarId <- conv $ freshIdentifierBase $ "ub"
  let upperBoundGradeVar = mkId upperBoundGradeVarId
  modify (\st -> st { tyVarContext = (upperBoundGradeVar, (k, InstanceQ)) : tyVarContext st })
  let upperBoundGrade = TyVar upperBoundGradeVar
  modifyPred $ addConstraintViaConjunction (Lub ns g1 g2 upperBoundGrade k)
  return upperBoundGrade

-- Version of computeJoin' where the inputs may be Nothing i.e.,
-- implicit 1 grade
computeJoin' :: (?globals :: Globals) => Maybe Kind -> Maybe Type -> Maybe Type -> Synthesiser (Maybe Type)
computeJoin' mKind mg1 mg2 = do
  x <- computeJoin mKind (getGradeFromArrow mg1) (getGradeFromArrow mg2)
  return $ Just x

gPlus :: Type -> Type -> Type
gPlus = TyInfix TyOpPlus

gTimes :: Type -> Type -> Type
gTimes = TyInfix TyOpTimes

exprFold :: Span -> Expr () () -> Expr () () -> Expr () ()
exprFold s newExpr (App s' a rf e1 e2) = App s' a rf (exprFold s newExpr e1) (exprFold s newExpr e2)
exprFold s newExpr (AppTy s' a rf e1 t) = AppTy s' a rf (exprFold s newExpr e1) t
exprFold s newExpr (Binop s' a b op e1 e2) = Binop s' a b op (exprFold s newExpr e1) (exprFold s newExpr e2)
exprFold s newExpr (LetDiamond s' a b ps mt e1 e2) = LetDiamond s' a b ps mt (exprFold s newExpr e1) (exprFold s newExpr e2)
exprFold s newExpr (TryCatch s' a b e p mt e1 e2) = TryCatch s' a b (exprFold s newExpr e) p mt (exprFold s newExpr e1) (exprFold s newExpr e2)
exprFold s newExpr (Val s' a b val) = Val s' a b (valueFold s newExpr val)
exprFold s newExpr (Case s' a b expr pats) = Case s' a b (exprFold s newExpr expr) pats
exprFold s newExpr (Hole s' a b ids hints) = if s == s' then newExpr else Hole s' a b ids hints


valueFold :: Span -> Expr () () -> Value () () -> Value () ()
valueFold s newExpr (Abs a pats mt e) = Abs a pats mt (exprFold s newExpr e)
valueFold s newExpr (Promote a e) = Promote a (exprFold s newExpr e)
valueFold s newExpr (Pure a e) = Pure a (exprFold s newExpr e)
valueFold s newExpr (Nec a e) = Nec a (exprFold s newExpr e)
valueFold s newExpr (Constr a ident vals) = Constr a ident $ map (valueFold s newExpr) vals
valueFold s newExpr v = v

  
