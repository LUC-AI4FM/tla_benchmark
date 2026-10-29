---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0..(N-1)

VARIABLES sem, pc

vars == << sem, pc >>

LeftFork(p)  == (p - 1 + N) % N
RightFork(p) == p

\* Philosopher 0 takes its left fork first; all others take their right fork first.
FirstFork(p)  == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

TypeOK ==
    /\ sem \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"e1", "e2", "e3", "e4", "e5"}]

Init ==
    /\ sem = [i \in Procs |-> 1]
    /\ pc = [self \in Procs |-> "e1"]

\* Acquire the first fork (P operation on a binary semaphore)
e1(self) ==
    /\ pc[self] = "e1"
    /\ sem[FirstFork(self)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

\* Acquire the second fork
e2(self) ==
    /\ pc[self] = "e2"
    /\ sem[SecondFork(self)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e3"]

\* Eat
e3(self) ==
    /\ pc[self] = "e3"
    /\ UNCHANGED sem
    /\ pc' = [pc EXCEPT ![self] = "e4"]

\* Release the first fork (V operation)
e4(self) ==
    /\ pc[self] = "e4"
    /\ sem' = [sem EXCEPT ![FirstFork(self)] = 1]
    /\ pc' = [pc EXCEPT ![self] = "e5"]

\* Release the second fork, then loop back
e5(self) ==
    /\ pc[self] = "e5"
    /\ sem' = [sem EXCEPT ![SecondFork(self)] = 1]
    /\ pc' = [pc EXCEPT ![self] = "e1"]

proc(self) == e1(self) \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : SF_vars(proc(self))

Eating(p) == pc[p] = "e3"

\* No two adjacent philosophers eat at the same time
Invariant ==
    \A i \in Procs : ~(Eating(i) /\ Eating((i + 1) % N) /\ i # (i + 1) % N)

\* Every philosopher eats infinitely often
StarvationFree ==
    \A p \in Procs : []<>(Eating(p))

=============================================================================