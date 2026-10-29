------------------------------ MODULE DiningPhilosophers ------------------------------
(***************************************************************************)
(* Dining Philosophers with N philosophers around a circular table.        *)
(* Philosopher p sits between fork p (its left fork) and fork (p+1) % N    *)
(* (its right fork).                                                       *)
(*                                                                         *)
(* The general model allows a philosopher to acquire its two forks one at  *)
(* a time, in an order fixed by a protocol. The two acquisition steps are  *)
(* parameterized by FirstFork(p) and SecondFork(p), so other protocols can *)
(* be substituted.                                                         *)
(*                                                                         *)
(* The implementation under consideration is the resource-hierarchy       *)
(* protocol: each philosopher acquires its lower-numbered fork first. This *)
(* protocol must satisfy safety, fork mutual exclusion, deadlock freedom   *)
(* and starvation freedom for every N >= 2.                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

VARIABLES state,  \* state[p] \in {"thinking", "hungry", "eating"}
          fork    \* fork[f] = holder of fork f, or NoOne

vars == <<state, fork>>

Phil  == 0 .. (N - 1)
Forks == 0 .. (N - 1)
NoOne == N   \* not a philosopher id

LeftFork(p)  == p
RightFork(p) == (p + 1) % N
LeftNeighbor(p)  == (p + N - 1) % N
RightNeighbor(p) == (p + 1) % N

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a < b THEN b ELSE a

(* Acquisition protocol: resource hierarchy (lower-numbered fork first). *)
FirstFork(p)  == Min(LeftFork(p), RightFork(p))
SecondFork(p) == Max(LeftFork(p), RightFork(p))

TypeOK ==
    /\ state \in [Phil -> {"thinking", "hungry", "eating"}]
    /\ fork \in [Forks -> Phil \cup {NoOne}]

Init ==
    /\ state = [p \in Phil |-> "thinking"]
    /\ fork  = [f \in Forks |-> NoOne]

(* A thinking philosopher decides to try to eat. *)
GetHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED fork

(* A hungry philosopher picks up its first fork if it is free. *)
TakeFirst(p) ==
    /\ state[p] = "hungry"
    /\ fork[FirstFork(p)] = NoOne
    /\ fork' = [fork EXCEPT ![FirstFork(p)] = p]
    /\ UNCHANGED state

(* A hungry philosopher holding its first fork picks up its second fork, *)
(* if free, and starts eating.                                            *)
TakeSecond(p) ==
    /\ state[p] = "hungry"
    /\ fork[FirstFork(p)] = p
    /\ fork[SecondFork(p)] = NoOne
    /\ fork' = [fork EXCEPT ![SecondFork(p)] = p]
    /\ state' = [state EXCEPT ![p] = "eating"]

(* An eating philosopher puts down both forks and resumes thinking. *)
Release(p) ==
    /\ state[p] = "eating"
    /\ fork' = [fork EXCEPT ![LeftFork(p)] = NoOne, ![RightFork(p)] = NoOne]
    /\ state' = [state EXCEPT ![p] = "thinking"]

Next ==
    \E p \in Phil :
        \/ GetHungry(p)
        \/ TakeFirst(p)
        \/ TakeSecond(p)
        \/ Release(p)

(***************************************************************************)
(* Fairness assumptions:                                                   *)
(*  - Weak fairness: a philosopher eventually gets hungry, and an eating   *)
(*    philosopher eventually releases its forks.                           *)
(*  - Strong fairness on fork acquisition: if a needed fork is free        *)
(*    infinitely often, the philosopher eventually gets it.                *)
(***************************************************************************)
Fairness ==
    \A p \in Phil :
        /\ WF_vars(GetHungry(p))
        /\ WF_vars(Release(p))
        /\ SF_vars(TakeFirst(p))
        /\ SF_vars(TakeSecond(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* No two adjacent philosophers eat simultaneously. *)
NoAdjacentEating ==
    \A p \in Phil :
        ~(state[p] = "eating" /\ state[RightNeighbor(p)] = "eating")

(* Each fork has at most one holder, and that holder is adjacent to the  *)
(* fork. The function representation forbids two holders.                *)
ForkMutex ==
    \A f \in Forks :
        fork[f] \in {NoOne, f, LeftNeighbor(f)}

(* An eating philosopher holds both of its forks. *)
EatingHoldsForks ==
    \A p \in Phil :
        state[p] = "eating" =>
            /\ fork[LeftFork(p)] = p
            /\ fork[RightFork(p)] = p

(* Only hungry or eating philosophers hold forks. *)
HoldersActive ==
    \A f \in Forks :
        fork[f] # NoOne => state[fork[f]] \in {"hungry", "eating"}

(* Deadlock freedom: some action is always enabled. *)
DeadlockFree ==
    \E p \in Phil :
        ENABLED (GetHungry(p) \/ TakeFirst(p) \/ TakeSecond(p) \/ Release(p))

Invariant ==
    /\ TypeOK
    /\ NoAdjacentEating
    /\ ForkMutex
    /\ EatingHoldsForks
    /\ HoldersActive
    /\ DeadlockFree

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every hungry philosopher eventually eats. *)
HungryEventuallyEats ==
    \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

(* Strong starvation freedom: every philosopher eats infinitely often. *)
StarvationFree ==
    \A p \in Phil : []<>(state[p] = "eating")

THEOREM Spec => []Invariant
THEOREM Spec => StarvationFree /\ HungryEventuallyEats

=============================================================================