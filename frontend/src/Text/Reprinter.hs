{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Text.Reprinter
  ( module Data.Functor.Identity
  , module Data.Generics
  , module Data.Generics.Zipper
  , Position
  , RefactorType(..)
  , Refactorable(..)
  , Reprinting
  , Source
  , Span
  , Line(..)
  , Col(..)
  , advanceCol
  , advanceLine
  , catchAll
  , genReprinting
  , initCol
  , initLine
  , initPosition
  , mkCol
  , mkLine
  , reprint
  , reprintSort
  ) where

-- Import solely for re-exporting for library clients
import Data.Functor.Identity
import Data.Generics
--

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Lazy
import Data.Generics.Zipper
import Data.List (sortOn)
import qualified Data.Text.Lazy as Text

-- | Text from source file
type Source = Text.Text

-- | A line within the source text
newtype Line = Line Int deriving (Data, Eq, Ord, Show)

-- | Lines start at 1
initLine :: Line
initLine = Line 1

-- | Smart constructor for a Line, checks that line >= 1
mkLine :: Int -> Either String Line
mkLine l
  | l < 1 = Left $ "mkLine: called with: " <> show l <> ". Minimum is 1."
  | otherwise = Right (Line  l)

-- | A column within the source text
newtype Col = Col Int deriving (Data, Eq, Ord, Show)

-- | Columns start at 1
initCol :: Col
initCol = Col 1

-- | Smart constructor for a Col, checks that column >= 1
mkCol :: Int -> Either String Col
mkCol l
  | l < 1 = Left $ "mkCol: called with: " <> show l <> ". Minimum is 1."
  | otherwise = Right (Col  l)

-- | A position in a text (imagine a cursor)
type Position = (Line,Col)

-- | The initial position
initPosition :: Position
initPosition = (initLine,initCol)

-- | Given a position, go down a line, going back to the initial column
advanceLine :: Position -> Position
advanceLine (Line x, _) = (Line (x+1), initCol)

-- | Given a position, advance by one column
advanceCol :: Position -> Position
advanceCol (ln, Col x) = (ln, Col (x+1))

-- | Two positions give the lower and upper bounds of a source span
type Span = (Position, Position)

-- | Type of a reprinting function
type Reprinting m = forall node . Typeable node => node -> m (Maybe (RefactorType, Source, Span))

-- | Specify a refactoring type
data RefactorType = Before | After | Replace
    deriving Show -- for debugging

-- | The reprint algorithm takes a refactoring (parameteric in
-- | some monad m) and turns an arbitrary pretty-printable type 'ast'
-- | into a monadic Source transformer.
reprint :: (Monad m, Data ast) => Reprinting m -> ast -> Source -> m Source
reprint reprinting ast input
  -- If the input is empty return empty
  | Text.null input = return mempty

  -- Otherwise proceed with the algorithm
  | otherwise = do
    -- Initial state comprises start cursor and input source
    let state_0 = (initPosition, input)
    -- Enter the top-node of a zipper for `ast'
    let comp = enter reprinting (toZipper ast)
    (out, (_, remaining)) <- runStateT comp state_0
    -- Add to the output source the remaining input source
    return (out <> remaining)

-- | Take a refactoring and a zipper producing a stateful Source transformer with Position state.
enter :: Monad m => Reprinting m -> Zipper ast -> StateT (Position, Source) m Source
enter reprinting zipper = do
    -- Step 1: Apply a refactoring
    refactoringInfo <- lift (query reprinting zipper)

    -- Step 2: Deal with refactored code or go to children
    output <- case refactoringInfo of
      -- No refactoring; go to children
      Nothing -> go down'
      -- A refactoring was applied
      Just r -> splice r
    -- Step 3: Enter the right sibling of the current context
    outputSib <- go right

    -- Finally append output of current context/children
    -- and right sibling
    return (output <> outputSib)

  where
    go direction =
        case direction zipper of
          -- Go to next node if there is one
          Just zipper -> enter reprinting zipper
          -- Otherwise return the empty string
          Nothing -> return mempty


-- | The reprint algorithm takes a refactoring (parameteric in
-- | some monad m) and turns an arbitrary pretty-printable type 'ast'
-- | into a monadic Source transformer.
reprintSort :: (Monad m, Data ast) => Reprinting m -> ast -> Source -> m Source
reprintSort reprinting ast input
  -- If the input is empty return empty
  | Text.null input = return mempty

  -- Otherwise proceed with the algorithm
  | otherwise = do
    -- Initial state comprises start cursor and input source
    let state_0 = (initPosition, input)
    -- Enter the top-node of a zipper for `ast'
    let comp = enter' reprinting (toZipper ast)
    (out, (_, remaining)) <- runStateT comp state_0
    -- Add to the output source the remaining input source
    return (out <> remaining)


-- | Take a refactoring and a zipper to produce a list of refactorings
enter' :: Monad m => Reprinting m -> Zipper ast
      -> StateT (Position, Source) m Source
enter' reprinting zipper = do
    -- Step 1: Get refactorings via AST zipper traversal
    rs <- lift $ getRefactorings reprinting zipper []
    -- Step 2: Do the splicing on the sorted refactorings
    srcs <- mapM splice (sortBySpan . reverse $ rs)
    return $ Text.concat srcs
  where
    sortBySpan = sortOn (\(_,_,sp) -> sp)

getRefactorings :: Monad m => Reprinting m -> Zipper ast -> [(RefactorType, Source, Span)]
                    -> m [(RefactorType, Source, Span)]
getRefactorings reprinting zipper acc = do
    -- Step 1: Apply a refactoring
    refactoringInfo <- query reprinting zipper
    -- Step 2: Deal with refactored code or go to children
    acc <- case refactoringInfo of
      -- No refactoring; go to children
      Nothing -> go down' acc
      -- A refactoring was applied, add it to the accumulator
      Just r -> return (r : acc)
    -- Step 3: Enter the left sibling of the current focus
    acc <- go right acc
    -- Finally return the accumulated refactorings
    return acc

  where
    go direction acc =
        case direction zipper of
          -- Go to next node if there is one
          Just zipper -> getRefactorings reprinting zipper acc
          -- Otherwise return the empty string
          Nothing -> return acc

splice :: Monad m => (RefactorType, Source, Span) -> StateT (Position, Source) m Source
splice (typ, output, (lb, ub)) = do
    (cursor, inp) <- get
    case typ of
      Replace -> do
        -- Get soure up to start of refactored node
        let (pre, inp') = splitBySpan (cursor, lb) inp
        -- Remove source covered by refactoring
        let (_, inp'') = splitBySpan (lb, ub) inp'
        put (ub, inp'')
        return (pre <> output)
      After -> do
        -- Get source up to end of the refactored node
        let (pre, inp') = splitBySpan (cursor, ub) inp
        put (ub, inp')
        return (pre <> output)
      Before -> do
        -- Get source up to start of refactored node
        let (pre, inp') = splitBySpan (cursor, lb) inp
        -- Discard portion consumed by the refactoring
        let (post, inp'') = splitBySpan (lb, ub) inp'
        put (ub, inp'')
        return (pre <> output <> post)

-- Given a lower-bound and upper-bound pair of Positions, split the
-- incoming Source based on the distance between the Position pairs
splitBySpan :: Span -> Source -> (Source, Source)
splitBySpan (lower, upper) =
    subtext mempty lower
  where
    subtext acc cursor input
      | cursor < lower =
          case Text.uncons input of
            Nothing -> done
            Just ('\n', input') -> subtext acc (advanceLine cursor) input'
            Just (_, input')    -> subtext acc (advanceCol cursor) input'
      | cursor < upper =
          case Text.uncons input of
            Nothing -> done
            Just ('\n', input') -> subtext (Text.cons '\n' acc) (advanceLine cursor) input'
            Just (x, input')    -> subtext (Text.cons x acc) (advanceCol cursor) input'
      | otherwise = done
      where done = (Text.reverse acc, input)



-- | Infrastructure for building the reprinter "plugins"
class Refactorable t where
  isRefactored :: t -> Maybe RefactorType
  getSpan      :: t -> Span

-- | Essentially wraps the refactorable interface
genReprinting :: (Monad m, Refactorable t)
              => (t -> m Source) -> t -> m (Maybe (RefactorType, Source, Span))
genReprinting f z = case isRefactored z of
    Nothing -> return Nothing
    Just refactorType -> do
      output <- f z
      return $ Just (refactorType, output, getSpan z)

-- | Catch all generic query
catchAll :: Monad m => a -> m (Maybe b)
catchAll _ = return Nothing