------------------------------ MODULE DiningPhilosophersCM ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Philosophers are P == 0..N-1 sitting on a ring.
  Forks are indexed by their lower-numbered endpoint: fork e connects e and Right(e).
*)

P == 0..(N-1)
Forks == P

Right(i) == (i + 1) \mod N
Left(i)  == (i + (N - 1)) \mod N

VARIABLES
  Owner,    \* function Forks -> P, Owner[e] \in {e, Right(e)}
  Dirty,    \* function Forks -> BOOLEAN, cleanliness of fork e
  Request,  \* function P -> SUBSET P, Request[i] is the set of neighbors i is requesting a fork from
  Hungry,   \* function P -> BOOLEAN, whether philosopher i is hungry
  Eating    \* function P -> BOOLEAN, whether philosopher i is currently eating (in critical section)

vars == << Owner, Dirty, Request, Hungry, Eating >>

Neighbors(i) == {Left(i), Right(i)}

Holds(i, e) == Owner[e] = i
BothHeld(i) == Holds(i, i) /\ Holds(i, Left(i))
BothClean(i) == ~Dirty[i] /\ ~Dirty[Left(i)]

TypeOK ==
  /\ Owner \in [Forks -> P]
  /\ \A e \in Forks : Owner[e] \in {e, Right(e)}
  /\ Dirty \in [Forks -> BOOLEAN]
  /\ Hungry \in [P -> BOOLEAN]
  /\ Eating \in [P -> BOOLEAN]
  /\ Request \in [P -> SUBSET P]
  /\ \A i \in P : Request[i] \subseteq Neighbors(i)

MutualExclusion ==
  \A i \in P : ~(Eating[i] /\ Eating[Right(i)])

Init ==
  /\ Owner = [e \in Forks |-> e]                         \* lower-numbered endpoint initially holds the fork
  /\ Dirty = [e \in Forks |-> TRUE]                      \* all forks start dirty
  /\ Request = [i \in P |-> {}]
  /\ Hungry  = [i \in P |-> FALSE]
  /\ Eating  = [i \in P |-> FALSE]
  /\ TypeOK

(*
  Requesting missing forks while hungry
*)
RequestRight(i) ==
  /\ i \in P
  /\ Hungry[i]
  /\ Owner[i] # i                                       \* right fork missing
  /\ Right(i) \notin Request[i]
  /\ Request' = [Request EXCEPT ![i] = @ \cup {Right(i)}]
  /\ UNCHANGED << Owner, Dirty, Hungry, Eating >>

RequestLeft(i) ==
  /\ i \in P
  /\ Hungry[i]
  /\ Owner[Left(i)] # i                                 \* left fork missing
  /\ Left(i) \notin Request[i]
  /\ Request' = [Request EXCEPT ![i] = @ \cup {Left(i)}]
  /\ UNCHANGED << Owner, Dirty, Hungry, Eating >>

(*
  Pass a fork to a requesting neighbor. In the Chandy-Misra scheme,
  the holder passes the fork only if it is dirty; the act of passing
  yields a clean fork to the receiver.
*)
PassRight(i) ==
  /\ i \in P
  /\ Owner[i] = i                                       \* i holds right fork e = i
  /\ Right(i) \in Request[Right(i)]                     \* right neighbor requests from i
  /\ Dirty[i]                                           \* pass only if dirty
  /\ Owner' = [Owner EXCEPT ![i] = Right(i)]
  /\ Dirty' = [Dirty EXCEPT ![i] = FALSE]               \* becomes clean at receiver
  /\ Request' = [Request EXCEPT ![Right(i)] = @ \ {i}]
  /\ UNCHANGED << Hungry, Eating >>

PassLeft(i) ==
  /\ i \in P
  /\ Owner[Left(i)] = i                                 \* i holds left fork e = Left(i)
  /\ i \in Request[Left(i)]                             \* left neighbor requests from i
  /\ Dirty[Left(i)]                                     \* pass only if dirty
  /\ Owner' = [Owner EXCEPT ![Left(i)] = Left(i)]
  /\ Dirty' = [Dirty EXCEPT ![Left(i)] = FALSE]         \* becomes clean at receiver
  /\ Request' = [Request EXCEPT ![Left(i)] = @ \ {i}]
  /\ UNCHANGED << Hungry, Eating >>

(*
  Eating is modeled as a two-phase critical section:
  StartEat enters the eating state; FinishEat leaves it and dirties both forks.
*)
StartEat(i) ==
  /\ i \in P
  /\ Hungry[i] /\ ~Eating[i]
  /\ BothHeld(i) /\ BothClean(i)
  /\ Eating' = [Eating EXCEPT ![i] = TRUE]
  /\ Hungry' = [Hungry EXCEPT ![i] = FALSE]
  /\ Request' = [Request EXCEPT ![i] = {}]              \* no longer requesting
  /\ UNCHANGED << Owner, Dirty >>

FinishEat(i) ==
  /\ i \in P
  /\ Eating[i]
  /\ Eating' = [Eating EXCEPT ![i] = FALSE]
  /\ Dirty' = [Dirty EXCEPT ![i] = TRUE, ![Left(i)] = TRUE]
  /\ UNCHANGED << Owner, Request, Hungry >>

(*
  Thinking to hungry transition to ensure philosophers keep cycling.
*)
BecomeHungry(i) ==
  /\ i \in P
  /\ ~Hungry[i] /\ ~Eating[i]
  /\ Hungry' = [Hungry EXCEPT ![i] = TRUE]
  /\ UNCHANGED << Owner, Dirty, Request, Eating >>

PhilosopherStep(i) ==
  RequestRight(i) \/
  RequestLeft(i)  \/
  PassRight(i)    \/
  PassLeft(i)     \/
  StartEat(i)     \/
  FinishEat(i)    \/
  BecomeHungry(i)

Next ==
  \E i \in P : PhilosopherStep(i)

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in P :
        WF_vars(RequestRight(i)) /\
        WF_vars(RequestLeft(i))  /\
        WF_vars(PassRight(i))    /\
        WF_vars(PassLeft(i))     /\
        WF_vars(FinishEat(i))    /\
        WF_vars(BecomeHungry(i))

=============================================================================