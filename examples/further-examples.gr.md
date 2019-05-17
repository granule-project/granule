Having seen the details of the type system, we provide some final
examples.

### Interaction with data structures

Graded modalities can be commuted with
other data types, for example to pull information about consumption of
sub-parts of data up to the whole, or
dually to push capabilities for consumption down to sub-parts of a data
type. Such notions are embodied by functions like the following
for commuting products with the
exact-usage graded modality:

~~~ granule
push : forall {a : Type, b : Type, n : Nat} . (a, b) [n] -> (a [n], b [n])
push [(x, y)] = ([x], [y])
~~~

~~~ granule
pull : forall {a : Type, b : Type, n : Nat} . (a [n], b [n]) -> (a, b) [n]
pull ([x], [y]) = [(x, y)]
~~~

In practice, combinators such as `push` and `pull` are
rarely used directly as we can instead use Granule's
pattern matching features over graded modalities, as in the
derivation of `push`/`pull`. For example, for
the safe head function on vectors can be defined:

~~~ granule
head : forall {a : Type, n : Type} . (Vec (n+1) a) [0..1] -> a
head [Cons x _] = x
~~~

The incoming vector has the capability to be consumed either `0`
or `1` times. By pattern matching, this capability is pushed
down to the sub-parts of the data such that every element can be used
`0..1` times, and every tail can be used `0..1`
times. This is utilised in the last pattern match where the tail of
the list (and subsequently all its elements) is discarded, as
indicated by the wildcard pattern inside of the unboxing pattern.

The Granule
[standard library](https://github.com/granule-project/granule/tree/master/StdLib)
provides a variety of data structures including graphs, lists, stacks,
vectors. Often we can characterise different design decisions for
data types via their graded modal types.

TODO: stack/peek here

### Grade interaction
To illustrate the interaction between different modalities,
consider a data type for storing patient
information of different privacy levels:

~~~ granule
data Patient = Patient (String [Public]) (String [Private])
~~~


where the first field gives the city for a patient (public information) and
the second field gives their name (private). We can
then define a function that extracts a list of cities
from a list of patients:


~~~ granule
import Vec  -- Granule's standard vector library
getCities : forall n. Vec n (Patient [0..1])  -> Vec n (String [Public])
getCities Nil = Nil;
getCities (Cons [Patient [city] [name]] ps) = Cons [city] (getCities ps)
~~~


Since we do not use all of the information in the patient record, we
declare the input as affine using an `Interval Nat` modality
with `0..1`. The base case (`Nil`) is
simple to understand, but in the inductive case
we see that the head of the input is `[Patient [city] [name]]`. Let us
remind ourselves of the meaning of these nested boxes by looking at the types:
the elements of the list are of type `Patient [0..1]` so the outer box
is tracking variable usage via `Nat` intervals; the elements of
the `Patient` value constructor are of type `String [Public]` and
`String [Private]` respectively, so both inner boxes are tracking security
level information via the lattice algebra we have seen before.
We can safely collect the cities and output a list of
public city names in out database.

$\mathsf{Flatten} \; (0..1) (\mathsf{Interval} \; \mathsf{Nat}) \;
\mathsf{Public} \; \mathsf{Level} = (0..1, \mathsf{Public})
: (\mathsf{Interval} \; \mathsf{Nat}) \times \mathsf{Level} ]]$.


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

The Granule interpreter gives the following type error:


### Session types

Granule supports *session
  types*
in the style of the GV calculus
leveraging linear types to embed session types primitives.
When combined with graded linearity, we can express novel communication
properties not supported by existing session type approaches.
Granule's builtin library provides channel primitives,
where `Com` is a trivial graded possibility modality for
capturing communication effects:


~~~ granule
data Protocol = Recv Type Protocol | Send Type Protocol | ...
send : forall { a : Type, s : Protocol } . Chan (Send a s) -> a -> (Chan s) <Com>
recv : forall { a : Type, s : Protocol } . Chan (Recv a s) -> (a, Chan s) <Com>
forkC : forall { s : Protocol, k : Coeffect, c : k } . ((Chan s) [c] -> () <Com>)
                                                 -> ((Chan (Dual s)) [c]) <Com>
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
sendVec : forall n a .
        (Chan (Send a End)) [n]
     -> Vec n a -> () <Com>
sendVec [c] Nil = pure ();
sendVec [c] (Cons x xs) =
  let c'  <- send c x;
      ()  <- close c'
  in sendVec [c] xs
~~~

~~~ granule
recvVec : forall n a .
  N n -> (Chan (Recv a End)) [n] -> (Vec n a) <Com>
recvVec Z [c] = pure Nil;
recvVec (S n) [c] =
  let (x, c') <- recv c;
      ()      <- close c';
      xs      <- recvVec n [c]
  in pure (Cons x xs)
~~~

On the left, `sendVec` has a channel which it can use
exactly `n` times to send values of type `a`,
taking a vector and sending each element on the channel.
Dually, `recvVec` takes a size `n` and a channel
which it uses `n` times to receive values of `a`,
collecting the results into an output vector. We can then
put these two processes together using `forkC`:


~~~ granule
example : forall {n : Nat, a : Type} . N n -> Vec n a -> (Vec n a) <Com>
example n list = let c <- forkC (\c -> sendVec c list) in recvVec n c
~~~

