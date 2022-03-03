{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Granule.Synthesis.Monad where

import Language.Granule.Context
import Language.Granule.Checker.Monad

import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Logic
import qualified System.Clock as Clock
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts (Substitution)
import Language.Granule.Syntax.Type (TypeScheme)
import Language.Granule.Syntax.Identifiers 

-- Data structure for collecting information about synthesis
data SynthesisData =
  SynthesisData {
    smtCallsCount             :: Integer
  , smtTime                   :: Double
  , proverTime                :: Double -- longer than smtTime as it includes compilation of predicates to SMT
  , theoremSizeTotal          :: Integer
  , pathsExplored             :: Integer
  , startTime                 :: Clock.TimeSpec
  , constructors              :: Ctxt (Ctxt (TypeScheme, Substitution), Bool)
  , currDef                   :: [Id]
  , elimDepthReached          :: Bool
  , introDepthReached         :: Bool
  , appDepthReached           :: Bool
  , predicateContext          :: PredContext
  }
  deriving Show


instance Semigroup SynthesisData where
 (SynthesisData calls stime time size paths startTime constructors currDef elimDepthReached introDepthReached appDepthReached predContext) <> (SynthesisData calls' stime' time' size' paths' startTime' constructors' currDef' elimDepthReached' introDepthReached' appDepthReached' predContext') =
    SynthesisData (calls + calls') (stime + stime') (time + time') (size + size') (paths + paths') (startTime + startTime') (constructors ++ constructors') (currDef ++ currDef') (elimDepthReached || elimDepthReached') (introDepthReached || introDepthReached') (appDepthReached || appDepthReached') (predContext)

instance Monoid SynthesisData where
  mempty  = SynthesisData 0 0 0 0 0 0 [] [] False False False Top
  mappend = (<>)

-- Synthesiser monad

newtype Synthesiser a = Synthesiser
  { unSynthesiser ::
      ExceptT (NonEmpty CheckerError) (StateT CheckerState (LogicT (StateT SynthesisData IO))) a }
  deriving (Functor, Applicative, MonadState CheckerState, MonadError (NonEmpty CheckerError))

-- Synthesiser always uses fair bind from LogicT
instance Monad Synthesiser where
  return = Synthesiser . return
  k >>= f =
    Synthesiser $ ExceptT (StateT
       (\s -> unSynth k s >>- (\(eb, s) ->
          case eb of
            Left r -> mzero
            Right b -> (unSynth . f) b s)))

     where
       unSynth m = runStateT (runExceptT (unSynthesiser m))

-- Monad transformer definitions

instance MonadIO Synthesiser where
  liftIO = conv . liftIO

runSynthesiser ::  Int -> Synthesiser a
  -> (CheckerState -> StateT SynthesisData IO [((Either (NonEmpty CheckerError) a), CheckerState)])
runSynthesiser index m s = do
  observeManyT index (runStateT (runExceptT (unSynthesiser m)) s)

conv :: Checker a -> Synthesiser a
conv (Checker k) =
  Synthesiser
    (ExceptT
         (StateT (\s -> lift $ lift (runStateT (runExceptT k) s))))

try :: Synthesiser a -> Synthesiser a -> Synthesiser a
try m n = do
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
    state {
      pathsExplored = 1 + pathsExplored state
      })
  Synthesiser $ ExceptT ((runExceptT (unSynthesiser m)) `interleave` (runExceptT (unSynthesiser n)))


none :: Synthesiser a
none = Synthesiser (ExceptT mzero)

maybeToSynthesiser :: Maybe (Ctxt a) -> Synthesiser (Ctxt a)
maybeToSynthesiser (Just x) = return x
maybeToSynthesiser Nothing = none

boolToSynthesiser :: Bool -> a -> Synthesiser a
boolToSynthesiser True x = return x
boolToSynthesiser False _ = none


getSynthState ::  Synthesiser (SynthesisData)
getSynthState = Synthesiser $ lift $ lift $ get

modifyPred :: PredContext -> Synthesiser ()
modifyPred pred = Synthesiser $ lift $ lift $ lift $ modify (\state -> 
  state {
    predicateContext = pred
        })
