------------------------------ MODULE DiningPhilosophers ------------------------------
(***************************************************************************)
(* Dining Philosophers.                                                    *)
(*                                                                         *)
(* N philosophers sit around a circular table, numbered 0..N-1.            *)
(* Fork i lies between philosopher i and philosopher (i+1) % N.            *)
(* Philosopher p's left fork is p and its right fork is (p+1) % N.         *)
(*                                                                         *)
(* Philosophers act asynchronously. Each step of Next is one action by     *)
(* one philosopher, chosen nondeterministically.                           *)
(*                                                                         *)
(* The spec does not fix a single fork-acquisition order. The constant     *)
(* Protocol selects which acquisition discipline is under consideration:  *)
(*   "Hierarchy" : resource ordering. A philosopher first takes the lower  *)
(*                 numbered of its two forks, then the higher one.         *)
(*   "Atomic"    : a philosopher takes both forks in one indivisible step, *)
(*                 and only when both are free.                            *)
(* Other protocols can be added as further disjuncts of Acquire(p). For    *)
(* every protocol and every N >= 2, the implementation under consideration *)
(* must be proved to satisfy the safety and liveness properties below.     *)
(* The THEOREMs at the end state these obligations.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,        \* number of philosophers (and forks)
          Protocol  \* fork-acquisition discipline under consideration

ASSUME NAssumption        == N \in Nat /\ N >= 2
ASSUME ProtocolAssumption == Protocol \in {"Hierarchy", "Atomic"}

Phil  == 0 .. (N - 1)
Forks == 0 .. (N - 1)

NoOne == N              \* marker for a free fork (N is not in Phil)

LeftFork(p)  == p
RightFork(p) == (p + 1) % N
MyForks(p)   == {LeftFork(p), RightFork(p)}

LeftNbr(p)   == (p + N - 1) % N
RightNbr(p)  == (p + 1) % N

\* Resource-hierarchy order: the lower-numbered fork is acquired first.
FirstFork(p)  == IF LeftFork(p) < RightFork(p) THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF LeftFork(p) < RightFork(p) THEN RightFork(p) ELSE LeftFork(p)

VARIABLES state,   \* state[p] \in {"thinking", "hungry", "eating"}
          holder   \* holder[f] \in Phil \cup {NoOne}

vars == <<state, holder>>

Holds(p, f) == holder[f] = p
IsFree(f)   == holder[f] = NoOne

-----------------------------------------------------------------------------
TypeOK ==
    /\ state  \in [Phil -> {"thinking", "hungry", "eating"}]
    /\ holder \in [Forks -> Phil \cup {NoOne}]

Init ==
    /\ state  = [p \in Phil |-> "thinking"]
    /\ holder = [f \in Forks |-> NoOne]

-----------------------------------------------------------------------------
(* Actions *)

\* A thinking philosopher decides to try to eat.
GetHungry(p) ==
    /\ state[p] = "thinking"
    /\ state'  = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED holder

\* Hierarchy protocol, step 1: take the lower-numbered fork.
TakeFirst(p) ==
    /\ Protocol = "Hierarchy"
    /\ state[p] = "hungry"
    /\ IsFree(FirstFork(p))
    /\ holder' = [holder EXCEPT ![FirstFork(p)] = p]
    /\ UNCHANGED state

\* Hierarchy protocol, step 2: take the higher-numbered fork and start eating.
TakeSecond(p) ==
    /\ Protocol = "Hierarchy"
    /\ state[p] = "hungry"
    /\ Holds(p, FirstFork(p))
    /\ IsFree(SecondFork(p))
    /\ holder' = [holder EXCEPT ![SecondFork(p)] = p]
    /\ state'  = [state EXCEPT ![p] = "eating"]

\* Atomic protocol: take both forks at once and start eating.
TakeBoth(p) ==
    /\ Protocol = "Atomic"
    /\ state[p] = "hungry"
    /\ IsFree(LeftFork(p))
    /\ IsFree(RightFork(p))
    /\ holder' = [holder EXCEPT ![LeftFork(p)]  = p,
                                ![RightFork(p)] = p]
    /\ state'  = [state EXCEPT ![p] = "eating"]

Acquire(p) == TakeFirst(p) \/ TakeSecond(p) \/ TakeBoth(p)

\* Stop eating, put down both forks, and return to thinking.
Release(p) ==
    /\ state[p] = "eating"
    /\ holder' = [holder EXCEPT ![LeftFork(p)]  = NoOne,
                                ![RightFork(p)] = NoOne]
    /\ state'  = [state EXCEPT ![p] = "thinking"]

PhilStep(p) == GetHungry(p) \/ Acquire(p) \/ Release(p)

Next == \E p \in Phil : PhilStep(p)

-----------------------------------------------------------------------------
(* Fairness / progress assumptions                                         *)
(*  - WF on GetHungry: a philosopher does not think forever, so it always  *)
(*    eventually tries to eat again.                                       *)
(*  - WF on Release: a philosopher does not eat forever.                   *)
(*  - SF on each acquisition step: a fork that is free infinitely often    *)
(*    is eventually granted to a waiting philosopher. Neighbours cannot    *)
(*    keep snatching it away forever.                                      *)
Fairness ==
    \A p \in Phil :
        /\ WF_vars(GetHungry(p))
        /\ WF_vars(Release(p))
        /\ SF_vars(TakeFirst(p))
        /\ SF_vars(TakeSecond(p))
        /\ SF_vars(TakeBoth(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Mutual exclusion on forks: no fork is held by two distinct philosophers.
ForkMutex ==
    \A f \in Forks : \A p, q \in Phil :
        (Holds(p, f) /\ Holds(q, f)) => p = q

\* A fork is only ever held by one of the two philosophers adjacent to it.
ForksHeldByNeighbours ==
    \A f \in Forks : ~IsFree(f) => f \in MyForks(holder[f])

\* An eating philosopher holds both of its forks.
EatingHoldsBothForks ==
    \A p \in Phil : state[p] = "eating" =>
        (Holds(p, LeftFork(p)) /\ Holds(p, RightFork(p)))

\* No two adjacent philosophers eat at the same time.
NoAdjacentEating ==
    \A p \in Phil : ~(state[p] = "eating" /\ state[RightNbr(p)] = "eating")

\* Deadlock freedom.
\* (1) It is never the case that every philosopher is hungry and none of
\*     them can acquire a fork.
NoGlobalStarvationState ==
    ~(\A p \in Phil : state[p] = "hungry" /\ ~ENABLED Acquire(p))

\* (2) Some step of the system is always enabled.
DeadlockFree == ENABLED Next

\* The classic circular wait never occurs: every philosopher holding exactly
\* one fork while waiting for the other.
NoCircularWait ==
    ~(\A p \in Phil :
        /\ state[p] = "hungry"
        /\ \E f \in MyForks(p) : Holds(p, f) /\ ~Holds(p, (CHOOSE g \in MyForks(p) : g # f)))

SafetyInvariant ==
    /\ TypeOK
    /\ ForkMutex
    /\ ForksHeldByNeighbours
    /\ EatingHoldsBothForks
    /\ NoAdjacentEating
    /\ NoGlobalStarvationState
    /\ DeadlockFree
    /\ NoCircularWait

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every attempt to eat eventually succeeds.
StarvationFree ==
    \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

\* Strong starvation freedom: every philosopher eats infinitely often.
EatsInfinitelyOften ==
    \A p \in Phil : []<>(state[p] = "eating")

\* The system as a whole keeps making progress.
SystemProgress == []<><<Next>>_vars

-----------------------------------------------------------------------------
(* Proof obligations: these must hold for every N >= 2 and for the chosen  *)
(* Protocol.                                                               *)

THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM ForkSafety       == Spec => []ForkMutex
THEOREM EatingSafety     == Spec => []NoAdjacentEating
THEOREM NoDeadlock       == Spec => [](DeadlockFree /\ NoGlobalStarvationState)
THEOREM AllSafety        == Spec => []SafetyInvariant
THEOREM NoStarvation     == Spec => StarvationFree
THEOREM StrongLiveness   == Spec => EatsInfinitelyOften
THEOREM Progress         == Spec => SystemProgress

=============================================================================