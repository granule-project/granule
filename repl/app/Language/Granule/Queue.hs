--------------------------------------------------------------------------
-- Functional Queues                                                    --
--                                                                      --
-- These are based on the definition found in Okasaki's "Purely         --
-- Functional Data Structures".                                         --
--                                                                      --
-- One unique tool this library comes with is a structural fixpoint     --
-- combinator over queues to make complex function definitions easier.  --
--------------------------------------------------------------------------

module Language.Granule.Queue where

data Queue a = Queue [a] [a]

toListQ :: Queue a -> [a]
toListQ (Queue f r) = f <> (reverse r)

fromList :: [a] -> Queue a
fromList [] = emptyQ
fromList ls = queue ls []

-- This instance allows us to use Haskell's built in foldl and foldr.
instance Foldable Queue where
    foldMap m = (foldMap m).toListQ

instance Show a => Show (Queue a) where
    show = show.toListQ

emptyQ :: Queue a
emptyQ = Queue [] []

headQ :: Queue a -> a
headQ (Queue (x:xs) _) = x
headQ (Queue [] _)     = error "Empty queue"

queue :: [a] -> [a] -> Queue a
queue [] r = Queue (reverse r) []
queue f r = Queue f r

enqueue :: a -> Queue a -> Queue a
enqueue elem (Queue f r) = (Queue (elem:f) r)

snoc :: Queue a -> a -> Queue a
snoc (Queue f r) x = queue f (x:r)

tailQ :: Queue a -> Queue a
tailQ (Queue (x:f) r) = queue f r
tailQ q@(Queue [] r)  = q

mapQ :: (a -> b) -> Queue a -> Queue b
mapQ m (Queue f r) = Queue (map m f) (map m r)


-- The following fixpoint operation makes it easier to do structural
-- recursion over queues.
--
--   fixQ q baseCase stepCase
--
-- The stepcase is a function that takes in the head of q, the tail of
-- q, and the recursive call.
--
-- For example, if we have the following queue:
--
-- testQ = snoc (snoc (snoc (snoc (snoc (snoc (snoc emptyQ 1) 2) 3) 4) 5) 6) 7
--
-- then we can output it to STDOUT as follows:
--
-- fixQ testQ (return ()) (\x q r -> (putStrLn.show $ x) >> r)

fixQ :: Queue a -> b -> (a -> Queue a -> b -> b) -> b
fixQ (Queue [] []) base _ = base
fixQ (Queue [] r) base step = fixQ (queue [] r) base step
fixQ (Queue (x:f) r) base step =
    let q = Queue f r
        in step x q (fixQ q base step)
