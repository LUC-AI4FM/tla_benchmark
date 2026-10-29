---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

\* Fork f is available iff sem[f] = 1.
\* Philosopher p sits between fork RightFork(p) and fork LeftFork(p).
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Asymmetric acquisition order: philosophers 1..N-1 take the right fork first,
\* philosopher 0 takes the left fork first.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in [Procs -> {0, 1}]
    /\ pc  \in [Procs -> {"l1", "l2", "e"}]

Init ==
    /\ sem = [f \in Procs |-> 1]
    /\ pc  = [p \in Procs |-> "l1"]

\* Acquire the first fork.
l1(self) ==
    /\ pc[self] = "l1"
    /\ sem[FirstFork(self)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 0]
    /\ pc'  = [pc  EXCEPT ![self] = "l2"]

\* Acquire the second fork.
l2(self) ==
    /\ pc[self] = "l2"
    /\ sem[SecondFork(self)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = 0]
    /\ pc'  = [pc  EXCEPT ![self] = "e"]

\* Eat, then release both forks and return to thinking.
e(self) ==
    /\ pc[self] = "e"
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 1, ![SecondFork(self)] = 1]
    /\ pc'  = [pc  EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ e(self)

Next == \E self \in Procs : Proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : SF_vars(Proc(self))

-----------------------------------------------------------------------------------

\* Safety: adjacent philosophers never eat at the same time.
MutualExclusion ==
    \A p \in Procs : (pc[p] = "e") => (pc[(p + 1) % N] # "e")

\* Liveness: every philosopher eats infinitely often.
StarvationFree ==
    \A p \in Procs : []<>(pc[p] = "e")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree
===================================================================================