------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

\* Fork p is philosopher p's right fork; fork (p+1) % N is the left fork.
\* Adjacent philosophers p and (p+1) % N share fork (p+1) % N.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* The fork each philosopher acquires first and second (asymmetric strategy)
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in [Procs -> {0, 1}]
    /\ pc  \in [Procs -> {"l0", "l1", "e"}]

Init ==
    /\ sem = [f \in Procs |-> 1]
    /\ pc  = [p \in Procs |-> "l0"]

\* l0: thinking; wait for and take the first fork
l0(self) ==
    /\ pc[self] = "l0"
    /\ sem[FirstFork(self)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "l1"]

\* l1: holding first fork; wait for and take the second fork
l1(self) ==
    /\ pc[self] = "l1"
    /\ sem[SecondFork(self)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "e"]

\* e: eating; release both forks and go back to thinking
e(self) ==
    /\ pc[self] = "e"
    /\ sem' = [sem EXCEPT ![RightFork(self)] = 1, ![LeftFork(self)] = 1]
    /\ pc'  = [pc EXCEPT ![self] = "l0"]

Proc(self) == l0(self) \/ l1(self) \/ e(self)

Next == \E self \in Procs : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Proc(self))

-----------------------------------------------------------------------------

\* Safety: adjacent philosophers never eat at the same time
MutualExclusion ==
    \A p \in Procs : ~(pc[p] = "e" /\ pc[(p + 1) % N] = "e")

\* Liveness: every philosopher eats infinitely often
StarvationFree ==
    \A p \in Procs : []<>(pc[p] = "e")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree

=============================================================================