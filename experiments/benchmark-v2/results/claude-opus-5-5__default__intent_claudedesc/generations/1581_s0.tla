---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES fork, pc

vars == << fork, pc >>

Procs == 0 .. (N - 1)

(* Fork p sits on philosopher p's right; fork (p+1) % N sits on their left. *)
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

(* Philosopher 0 is the asymmetric one: it takes the left fork first.     *)
(* Every other philosopher takes the right fork first.                    *)
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

(* Each fork is a binary semaphore: 1 means available, 0 means held. *)
TypeOK ==
    /\ fork \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"first", "second", "eat"}]

Init ==
    /\ fork = [f \in Procs |-> 1]
    /\ pc = [p \in Procs |-> "first"]

(* P(sem) on the first fork. *)
AcquireFirst(p) ==
    /\ pc[p] = "first"
    /\ fork[FirstFork(p)] = 1
    /\ fork' = [fork EXCEPT ![FirstFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "second"]

(* P(sem) on the second fork. *)
AcquireSecond(p) ==
    /\ pc[p] = "second"
    /\ fork[SecondFork(p)] = 1
    /\ fork' = [fork EXCEPT ![SecondFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eat"]

(* Eat, then V(sem) on both forks and loop back. *)
EatAndRelease(p) ==
    /\ pc[p] = "eat"
    /\ fork' = [fork EXCEPT ![FirstFork(p)] = 1, ![SecondFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "first"]

Proc(p) == AcquireFirst(p) \/ AcquireSecond(p) \/ EatAndRelease(p)

Next == \E p \in Procs : Proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : SF_vars(Proc(p))

-----------------------------------------------------------------------------------

(* Safety: no two adjacent philosophers eat at the same time. *)
MutualExclusion ==
    \A p \in Procs :
        (N > 1 /\ pc[p] = "eat") => pc[(p + 1) % N] # "eat"

(* Liveness: every philosopher eats infinitely often (starvation freedom). *)
StarvationFreedom ==
    \A p \in Procs : []<>(pc[p] = "eat")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
===================================================================================