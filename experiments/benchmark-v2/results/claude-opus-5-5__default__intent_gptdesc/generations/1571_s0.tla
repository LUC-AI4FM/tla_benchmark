------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining Philosophers, specified abstractly.                              *)
(*                                                                         *)
(* N philosophers, numbered 0..N-1, sit around a circular table.           *)
(*   - Fork f lies between philosopher f and philosopher (f-1) mod N.      *)
(*   - Philosopher p uses its left fork p and its right fork (p+1) mod N.  *)
(*   - Each fork is a binary shared resource: it is either free (NoOne)    *)
(*     or held by exactly one philosopher.                                 *)
(*                                                                         *)
(* Philosophers cycle thinking -> hungry -> eating -> thinking.            *)
(*   - Acquire: a hungry philosopher takes both adjacent forks in one      *)
(*     step, and only when both are free.                                  *)
(*   - Release: an eating philosopher returns both forks.                  *)
(*                                                                         *)
(* No global locking order is imposed. Contention between hungry           *)
(* neighbours is resolved by an abstract per-fork precedence (courtesy)    *)
(* relation:                                                               *)
(*   - A hungry philosopher may not take a fork from a hungry neighbour    *)
(*     that currently has precedence on that fork.                         *)
(*   - After eating, a philosopher yields precedence on both its forks     *)
(*     to its neighbours.                                                  *)
(* Weak fairness on every action makes each philosopher keep getting       *)
(* opportunities to progress.                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES state,   \* state[p] \in {"thinking","hungry","eating"}
          fork,    \* fork[f]  \in Phil \cup {NoOne}: current holder
          prio     \* prio[f]  \in Phil: which user of fork f has precedence

vars == <<state, fork, prio>>

Phil  == 0 .. (N - 1)
Forks == 0 .. (N - 1)
NoOne == -1

LeftFork(p)  == p
RightFork(p) == (p + 1) % N
ForksOf(p)   == {LeftFork(p), RightFork(p)}

RightNeighbor(p) == (p + 1) % N

(* The two philosophers sharing fork f *)
Users(f) == {f, (f + N - 1) % N}

(* The other philosopher sharing fork f with p *)
Other(f, p) == IF p = f THEN (f + N - 1) % N ELSE f

----------------------------------------------------------------------------
TypeOK ==
    /\ state \in [Phil -> {"thinking", "hungry", "eating"}]
    /\ fork  \in [Forks -> Phil \cup {NoOne}]
    /\ prio  \in [Forks -> Phil]
    /\ \A f \in Forks : prio[f] \in Users(f)

(* Initial precedence is acyclic: each fork goes to its lower-numbered user. *)
Init ==
    /\ state = [p \in Phil |-> "thinking"]
    /\ fork  = [f \in Forks |-> NoOne]
    /\ prio  = [f \in Forks |-> IF f = 0 THEN 0 ELSE f - 1]

----------------------------------------------------------------------------
(* A thinking philosopher decides to try to eat. *)
GetHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED <<fork, prio>>

(* Abstract acquire: take both adjacent forks atomically, only when both  *)
(* are free, and only without overriding a hungry neighbour's precedence. *)
Eat(p) ==
    /\ state[p] = "hungry"
    /\ \A f \in ForksOf(p) : fork[f] = NoOne
    /\ \A f \in ForksOf(p) : prio[f] = p \/ state[Other(f, p)] # "hungry"
    /\ fork'  = [f \in Forks |-> IF f \in ForksOf(p) THEN p ELSE fork[f]]
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED prio

(* Abstract release: return both forks to the free state and yield      *)
(* precedence on them to the neighbours.                                 *)
Release(p) ==
    /\ state[p] = "eating"
    /\ fork'  = [f \in Forks |-> IF f \in ForksOf(p) THEN NoOne ELSE fork[f]]
    /\ prio'  = [f \in Forks |-> IF f \in ForksOf(p) THEN Other(f, p) ELSE prio[f]]
    /\ state' = [state EXCEPT ![p] = "thinking"]

Next == \E p \in Phil : GetHungry(p) \/ Eat(p) \/ Release(p)

Fairness ==
    \A p \in Phil :
        /\ WF_vars(GetHungry(p))
        /\ WF_vars(Eat(p))
        /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* No two adjacent philosophers eat simultaneously. *)
MutualExclusion ==
    \A p \in Phil :
        (N > 1 /\ state[p] = "eating") => state[RightNeighbor(p)] # "eating"

(* Each fork is held by at most one philosopher. This is structural in    *)
(* the encoding; it is stated explicitly here, together with the holder   *)
(* being a user of that fork.                                             *)
ForkExclusive ==
    \A f \in Forks :
        fork[f] # NoOne =>
            /\ fork[f] \in Users(f)
            /\ \A p, q \in Phil : (fork[f] = p /\ fork[f] = q) => p = q

(* A fork is held iff one of its users is eating. Forks are therefore    *)
(* free whenever no adjacent philosopher is eating, i.e. they are         *)
(* returned after eating.                                                 *)
ForkIntegrity ==
    /\ \A p \in Phil : state[p] = "eating" =>
            \A f \in ForksOf(p) : fork[f] = p
    /\ \A f \in Forks : fork[f] # NoOne => state[fork[f]] = "eating"
    /\ \A p \in Phil : state[p] # "eating" =>
            \A f \in ForksOf(p) : fork[f] # p

(* Absence of deadlock: some philosopher can always take a step. *)
DeadlockFreedom == ENABLED Next

(* Absence of circular wait: it is never the case that every philosopher *)
(* is hungry and none of them can acquire its forks.                      *)
NoCircularWait ==
    ~ (\A p \in Phil : state[p] = "hungry" /\ ~ ENABLED Eat(p))

SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ForkExclusive
    /\ ForkIntegrity
    /\ DeadlockFreedom
    /\ NoCircularWait

----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

(* Every hungry philosopher eventually eats. *)
NoStarvation ==
    \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

(* Starvation-freedom: every philosopher eats infinitely often. *)
StarvationFreedom ==
    \A p \in Phil : []<>(state[p] = "eating")

(* Forks are always eventually returned after eating. *)
ForksReturned ==
    \A f \in Forks : (fork[f] # NoOne) ~> (fork[f] = NoOne)

(* The system as a whole keeps making progress. *)
Progress ==
    []<>(\E p \in Phil : state[p] = "eating")

----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => NoStarvation /\ StarvationFreedom /\ ForksReturned /\ Progress
=============================================================================