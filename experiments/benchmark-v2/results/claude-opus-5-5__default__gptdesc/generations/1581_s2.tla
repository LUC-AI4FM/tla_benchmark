---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)
Forks == 0 .. (N - 1)

\* Philosopher p's right fork is fork p; its left fork is fork (p+1) % N.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Asymmetric acquisition order: philosophers 1..N-1 take right then left,
\* philosopher 0 takes left then right.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

VARIABLES pc, sem

vars == << pc, sem >>

TypeOK ==
    /\ pc \in [Procs -> {"l0", "l1", "e"}]
    /\ sem \in [Forks -> {0, 1}]

Init ==
    /\ sem = [f \in Forks |-> 1]
    /\ pc = [p \in Procs |-> "l0"]

\* Thinking: acquire the first fork.
l0(self) ==
    /\ pc[self] = "l0"
    /\ sem[FirstFork(self)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 0]
    /\ pc' = [pc EXCEPT ![self] = "l1"]

\* Holding the first fork: acquire the second fork.
l1(self) ==
    /\ pc[self] = "l1"
    /\ sem[SecondFork(self)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e"]

\* Eating: release both forks and go back to thinking.
e(self) ==
    /\ pc[self] = "e"
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 1, ![SecondFork(self)] = 1]
    /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ e(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : SF_vars(proc(self))

-----------------------------------------------------------------------------

\* Safety: adjacent philosophers never eat at the same time.
MutualExclusion ==
    \A p \in Procs : ~(pc[p] = "e" /\ pc[(p + 1) % N] = "e")

\* Liveness: every philosopher eats infinitely often.
StarvationFree ==
    \A p \in Procs : []<>(pc[p] = "e")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree
=============================================================================