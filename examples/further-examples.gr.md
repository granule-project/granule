This file is based on Section 8 of the ICFP 2019 paper _Quantitative program
reasoning with graded modal types_.
Please refer to the paper for the technical details and a formalisation of the
overall system.

### Interaction with data structures

Graded modalities can be commuted with other data types, for example
to pull information about consumption of sub-parts of data up to the
whole, or dually to push capabilities for consumption down to
sub-parts of a data type. Such notions are embodied by functions like
the following for commuting products with the exact-usage graded
modality:

~~~ granule
pushPair : forall {a : Type, b : Type, k : Coeffect, c : k} . (a × b) [c] -> a [c] × b [c]
pushPair [(x, y)] = ([x], [y])
~~~

~~~ granule
pullPair : forall {a : Type, b : Type, k : Coeffect, c : k} . a [c] × b [c] -> (a × b) [c]
pullPair ([x], [y]) = [(x, y)]
~~~

In practice, combinators such as `pushPair` and `pullPair` are rarely
used directly as we can instead use Granule's pattern matching
features over graded modalities, as in the derivation of
`pushPair`/`pullPair`. For example, for the safe head function on
vectors can be defined:

~~~ granule
import Vec

-- called `head` in the `Vec` library, but renamed here for example
safeHead : forall {a : Type, n : Nat} . (Vec (n+1) a) [0..1] -> a
safeHead [Cons x _] = x
~~~

The incoming vector has the capability to be consumed either `0` or
`1` times. By pattern matching, this capability is pushed down to the
sub-parts of the data such that every element can be used `0..1`
times, and every tail can be used `0..1` times. This is utilised in
the last pattern match where the tail of the list (and subsequently
all its elements) is discarded, as indicated by the wildcard pattern
inside of the unboxing pattern.

The Granule
[standard library](https://github.com/granule-project/granule/tree/master/StdLib)
provides a variety of data structures including graphs, lists, stacks,
vectors. There are often different design decisions for the interaction
of data structures and graded modal types. For example, we represent
stacks with vectors with _pop_ and _push_ as dual linear operations
corresponding to cons and uncons:

~~~ granule
pop : forall {n : Nat, a : Type} . Vec (n+1) a -> (a, Vec n a)
pop = uncons

push : forall {n : Nat, a : Type} . a -> Vec n a -> Vec (n+1) a
push = Cons
~~~

The peek operation is more interesting as it is non-linear: we need to
use the head element twice:

~~~ granule
peek : forall {n : Nat, a : Type} . (Vec (n+1) a) [1..2] -> (a, Vec (n+1) a)
peek [Cons x xs] = (x, Cons x xs)
~~~

This corresponds to a kind of implicit \emph{push}: we have the
capability to use every component of the stack once or twice. In the
case of the head element `x`, we use it twice, and in the case of the
rest of the stack `xs` we use it once. An alternate definition of
`peek` provides a linear interface for the stack structure, but with
non-linearity on the elements:

~~~ granule
peek' : forall m : Ext Nat, a, n . Vec (n+1) (a [m..m+1]) -> (a, Vec (n+1) (a [m..m]))
peek' (Cons [x] xs) = (x, Cons [x] xs)
~~~

The type explains that we have a stack whose elements can be used
`m` to `m+1` times and we use this capability to copy
the head element returning a pair of the head and a stack whose
elements can now be used `m` to `m`.  This type is
useful for chaining together operations which operate on the elements
of the stack non-linearly. The former `peek` definition is more
suited to situations where the whole stack is being manipulated
non-linearly, rather than just its elements. Exploring the design
space and trade-offs for data structure libraries is further work.

### Grade interaction
To illustrate the interaction between different modalities,
consider a data type for storing patient
information of different privacy levels:

~~~ granule
data Patient = Patient (String [Public]) (String [Private])
~~~

where the first field gives the city for a patient (public information) and
the second field gives their name (private). We can
then define a function that, e.g., extracts a sample of cities
from a list of patients:


~~~ granule
import Vec  -- Granule's standard vector library
sampleCities : forall n k . N k -> (Vec (n+k) Patient) [0..1] -> Vec k (String [Public])
sampleCities Z [_] = Nil;
sampleCities (S n) [Cons (Patient [city] [name]) ps] = Cons [city] (sampleCities n [ps])
~~~

Since we do not use all of the information in the vector, we declare
the input as affine using an `Interval Nat` modality with `0..1`. The
base case (`Nil`) is straightfoward.

This demonstrates the use of different nested graded modalities.  The
outer modality declares that the input vector is affine, since we do
not necessarily use all its elements, given by an `Interval Nat`
modality with `0..1`.  The inner modalities provide the security
levels of patient information.  In the inductive case, we thus get
`ps` graded by `0..1` and by flattening `city` and `name` are graded
by products `(0..1, Public)` and `(0..1, Private)` respectively.  We
can safely collect the cities and output a list of public city names
in out database.

~~~ grill
import Vec
data Patient = Patient (String [Public]) (String [Private])
~~~

Let us see what happens when we try to accumulate the private name fields into a list
of public data:

~~~ grill
getCitiesBad : forall n. Vec n (Patient [0..1]) -> Vec n (String [Public])
getCitiesBad Nil = Nil;
getCitiesBad (Cons [Patient [city] [name]] ps) = Cons [name] (getCitiesBad ps)
~~~
(`gr examples/further-examples.gr.md --literate-env-name grill`)

The Granule checker gives the following type error, showing the
privacy violation:

     Grading error: 3:54:
     Private value cannot be moved to level Public.

### Session types

Granule supports *session types* in the style of the GV calculus
leveraging linear types to embed session types primitives.  When
combined with graded linearity, we can express novel communication
properties not supported by existing session type approaches.
Granule's builtin library provides channel primitives, where `Session` is
a trivial graded possibility modality for capturing communication
effects:


~~~
data Protocol = Recv Type Protocol | Send Type Protocol | ...
send : forall { a : Type, s : Protocol } . Chan (Send a s) -> a -> (Chan s) <Session>
recv : forall { a : Type, s : Protocol } . Chan (Recv a s) -> (a, Chan s) <Session>
forkC : forall { s : Protocol, k : Coeffect, c : k } . ((Chan s) [c] -> () <Session>)
                                                 -> ((Chan (Dual s)) [c]) <Session>
~~~

where `Dual : Protocol -> Protocol` computes the dual of a protocol.
 fork : forall { s : Protocol } . (Chan s -> Session ()) -> Session (Chan (Dual s))

Thus,  `send` takes a channel on which an `a` can be
sent, returning a channel on which behaviour `s` can then
be carried out. Similarly, `recv` takes a channel
on which one can receive an `a` value, getting back (in a pair)
the continuation channel `Chan n`. The `forkC`
primitive is higher-order, taking a function that uses a
channel in a way captured by some graded modality with grade
`c`, producing
a session computation. A channel with dual capabilities is returned,
that can also be used in a way captured by the grade `c`.

We can use these primitives to capture precisely-bounded replication
in protocols:

~~~ granule
sendVec : forall n a . (Chan (Send a End)) [n] -> Vec n a -> () <Session>
sendVec [c] Nil = pure ();
sendVec [c] (Cons x xs) =
  let c'  <- send c x;
      ()  <- close c'
  in sendVec [c] xs
~~~

~~~ granule
recvVec : forall n a . N n -> (Chan (Recv a End)) [n] -> (Vec n a) <Session>
recvVec Z [c] = pure Nil;
recvVec (S n) [c] =
  let (x, c') <- recv c;
      ()      <- close c';
      xs      <- recvVec n [c]
  in pure (Cons x xs)
~~~

On the left, `sendVec` has a channel which it can use exactly `n`
times to send values of type `a`, taking a vector and sending each
element on the channel.  Dually, `recvVec` takes a size `n` and a
channel which it uses `n` times to receive values of `a`, collecting
the results into an output vector. We can then put these two processes
together using `forkC`:

~~~ granule
example : forall {n : Nat, a : Type} . N n -> Vec n a -> (Vec n a) <Session>
example n list = let c <- forkC (\c -> sendVec c list) in recvVec n c
~~~
