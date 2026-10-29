------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

\* Fork indexing: philosopher i's left fork is fork i,
\* and its right fork is fork (i + 1) % N.
LeftFork(i)  == i
RightFork(i) == (i + 1) % N

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"l1", "l2", "l3", "l4", "l01", "l02", "l03", "l04"}]

Init ==
    /\ sem = [f \in Procs |-> 1]
    /\ pc  = [self \in Procs |-> IF self = 0 THEN "l01" ELSE "l1"]

----------------------------------------------------------------------------------------
\* Philosophers 1 .. N-1: acquire right fork, then left fork.

l1(self) ==
    /\ pc[self] = "l1"
    /\ sem[RightFork(self)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "l2"]

l2(self) ==
    /\ pc[self] = "l2"
    /\ sem[LeftFork(self)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "l3"]

\* At l3 the philosopher is eating; it then releases its right fork.
l3(self) ==
    /\ pc[self] = "l3"
    /\ sem' = [sem EXCEPT ![RightFork(self)] = 1]
    /\ pc'  = [pc EXCEPT ![self] = "l4"]

l4(self) ==
    /\ pc[self] = "l4"
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = 1]
    /\ pc'  = [pc EXCEPT ![self] = "l1"]

Phil(self) == l1(self) \/ l2(self) \/ l3(self) \/ l4(self)

----------------------------------------------------------------------------------------
\* Philosopher 0: acquire left fork, then right fork.

l01(self) ==
    /\ pc[self] = "l01"
    /\ sem[LeftFork(self)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "l02"]

l02(self) ==
    /\ pc[self] = "l02"
    /\ sem[RightFork(self)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "l03"]

\* At l03 philosopher 0 is eating; it then releases its left fork.
l03(self) ==
    /\ pc[self] = "l03"
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = 1]
    /\ pc'  = [pc EXCEPT ![self] = "l04"]

l04(self) ==
    /\ pc[self] = "l04"
    /\ sem' = [sem EXCEPT ![RightFork(self)] = 1]
    /\ pc'  = [pc EXCEPT ![self] = "l01"]

Phil0(self) == l01(self) \/ l02(self) \/ l03(self) \/ l04(self)

----------------------------------------------------------------------------------------

Proc(self) == IF self = 0 THEN Phil0(self) ELSE Phil(self)

Next == \E self \in Procs : Proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : SF_vars(Proc(self))

----------------------------------------------------------------------------------------

Eating(i) == IF i = 0 THEN pc[i] = "l03" ELSE pc[i] = "l3"

Invariant ==
    /\ TypeOK
    /\ \A i \in Procs : ~(Eating(i) /\ Eating((i + 1) % N))

StarvationFree == \A i \in Procs : []<>Eating(i)

=========================================================================================