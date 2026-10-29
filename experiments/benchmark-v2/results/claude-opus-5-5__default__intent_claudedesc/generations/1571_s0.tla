---------------------------- MODULE DiningPhilosophers ----------------------------
(***************************************************************************)
(* Dining Philosophers with asymmetric fork acquisition.                   *)
(* N philosophers sit around a circular table. Fork f lies between         *)
(* philosopher f and philosopher (f+1) % N.                                *)
(*   LeftFork(p)  == p                                                     *)
(*   RightFork(p) == (p+1) % N                                             *)
(* Forks are binary semaphores: 1 = available, 0 = taken.                  *)
(* Philosophers 1..N-1 acquire their right fork first, then their left.    *)
(* Philosopher 0 acquires its left fork first, then its right.             *)
(* This asymmetry breaks the circular-wait deadlock.                       *)
(* Model-check with N = 4.                                                 *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Phil == 0..(N-1)
Forks == 0..(N-1)

LeftFork(p)  == p
RightFork(p) == (p + 1) % N

FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

LeftNeighbor(p)  == (p + N - 1) % N
RightNeighbor(p) == (p + 1) % N

VARIABLES fork, pc

vars == <<fork, pc>>

PCStates == {"think", "acq1", "acq2", "eat"}

TypeOK ==
    /\ fork \in [Forks -> {0, 1}]
    /\ pc \in [Phil -> PCStates]

Init ==
    /\ fork = [f \in Forks |-> 1]
    /\ pc = [p \in Phil |-> "think"]

(* Finish thinking and become hungry *)
Think(p) ==
    /\ pc[p] = "think"
    /\ pc' = [pc EXCEPT ![p] = "acq1"]
    /\ UNCHANGED fork

(* P operation on first semaphore *)
AcquireFirst(p) ==
    /\ pc[p] = "acq1"
    /\ fork[FirstFork(p)] = 1
    /\ fork' = [fork EXCEPT ![FirstFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "acq2"]

(* P operation on second semaphore *)
AcquireSecond(p) ==
    /\ pc[p] = "acq2"
    /\ fork[SecondFork(p)] = 1
    /\ fork' = [fork EXCEPT ![SecondFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eat"]

(* Eat, then V operations on both semaphores *)
Release(p) ==
    /\ pc[p] = "eat"
    /\ fork' = [fork EXCEPT ![FirstFork(p)] = 1, ![SecondFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "think"]

Proc(p) ==
    \/ Think(p)
    \/ AcquireFirst(p)
    \/ AcquireSecond(p)
    \/ Release(p)

Next == \E p \in Phil : Proc(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Phil : SF_vars(Proc(p))

-----------------------------------------------------------------------------
(* Safety properties *)

Eating(p) == pc[p] = "eat"

Holds(p, f) ==
    \/ (f = FirstFork(p)  /\ pc[p] \in {"acq2", "eat"})
    \/ (f = SecondFork(p) /\ pc[p] = "eat")

(* No two adjacent philosophers eat simultaneously *)
MutualExclusion ==
    \A p \in Phil : Eating(p) => ~Eating(RightNeighbor(p))

(* No fork is held by two philosophers at once *)
ForkExclusion ==
    \A f \in Forks : \A p, q \in Phil :
        (p # q /\ Holds(p, f)) => ~Holds(q, f)

(* Semaphore value is consistent with fork ownership *)
SemaphoreConsistency ==
    \A f \in Forks : (fork[f] = 0) <=> (\E p \in Phil : Holds(p, f))

(* An eating philosopher holds both of its adjacent forks *)
EatingHoldsBothForks ==
    \A p \in Phil : Eating(p) =>
        /\ fork[LeftFork(p)] = 0
        /\ fork[RightFork(p)] = 0

(* No deadlock: some philosopher can always move *)
DeadlockFreedom == \E p \in Phil : ENABLED Proc(p)

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every philosopher eats infinitely often *)
StarvationFreedom == \A p \in Phil : []<>Eating(p)

(* Every hungry philosopher eventually eats *)
HungryEventuallyEats ==
    \A p \in Phil : (pc[p] = "acq1") ~> Eating(p)

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ ForkExclusion
                   /\ SemaphoreConsistency /\ EatingHoldsBothForks)
THEOREM Spec => StarvationFreedom

=============================================================================