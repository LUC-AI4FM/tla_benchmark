------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0 .. N-1

(* Fork p lies to the right of philosopher p; fork (p+1) % N to the left. *)
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

(* Asymmetric acquisition order: philosopher 0 takes left then right,
   all others take right then left. *)
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

VARIABLES pc, sem

vars == << pc, sem >>

TypeOK ==
    /\ pc  \in [Procs -> {"l0", "l1", "e", "l2"}]
    /\ sem \in [Procs -> {0, 1}]

Init ==
    /\ sem = [f \in Procs |-> 1]
    /\ pc  = [p \in Procs |-> "l0"]

(* Acquire the first fork *)
l0(self) ==
    /\ pc[self] = "l0"
    /\ sem[FirstFork(self)] > 0
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = @ - 1]
    /\ pc'  = [pc  EXCEPT ![self] = "l1"]

(* Acquire the second fork *)
l1(self) ==
    /\ pc[self] = "l1"
    /\ sem[SecondFork(self)] > 0
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = @ - 1]
    /\ pc'  = [pc  EXCEPT ![self] = "e"]

(* Eat *)
e(self) ==
    /\ pc[self] = "e"
    /\ pc'  = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED sem

(* Release both forks and go back to thinking *)
l2(self) ==
    /\ pc[self] = "l2"
    /\ sem' = [sem EXCEPT ![FirstFork(self)]  = @ + 1,
                          ![SecondFork(self)] = @ + 1]
    /\ pc'  = [pc  EXCEPT ![self] = "l0"]

Proc(self) == l0(self) \/ l1(self) \/ e(self) \/ l2(self)

Next == \E self \in Procs : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Proc(self))

-----------------------------------------------------------------------------------------

(* Safety: adjacent philosophers never eat at the same time *)
MutualExclusion ==
    \A p \in Procs : ~(pc[p] = "e" /\ pc[(p + 1) % N] = "e")

(* Liveness: every philosopher eats infinitely often *)
StarvationFree ==
    \A p \in Procs : []<>(pc[p] = "e")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree
=========================================================================================