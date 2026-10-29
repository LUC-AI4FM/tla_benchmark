------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 2

Phils == 0 .. (NP - 1)

\* Fork p is shared by philosopher p and philosopher (p-1) mod NP.
RightFork(p) == p
LeftFork(p)  == (p + 1) % NP

VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == (1 .. (NP - 1)) \cup {0}

Init == /\ sem = [f \in Phils |-> 1]
        /\ pc  = [self \in ProcSet |-> "L0"]

-----------------------------------------------------------------------------
\* Philosophers 1..NP-1: take right fork, then left fork, eat, release both.

L0(self) == /\ pc[self] = "L0"
            /\ sem[RightFork(self)] = 1
            /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ sem[LeftFork(self)] = 1
            /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "E"]

E(self) == /\ pc[self] = "E"
           /\ sem' = [sem EXCEPT ![RightFork(self)] = 1, ![LeftFork(self)] = 1]
           /\ pc'  = [pc EXCEPT ![self] = "L0"]

P(self) == L0(self) \/ L1(self) \/ E(self)

-----------------------------------------------------------------------------
\* Philosopher 0: take left fork, then right fork, eat, release both.

L0_0 == /\ pc[0] = "L0"
        /\ sem[LeftFork(0)] = 1
        /\ sem' = [sem EXCEPT ![LeftFork(0)] = 0]
        /\ pc'  = [pc EXCEPT ![0] = "L1"]

L1_0 == /\ pc[0] = "L1"
        /\ sem[RightFork(0)] = 1
        /\ sem' = [sem EXCEPT ![RightFork(0)] = 0]
        /\ pc'  = [pc EXCEPT ![0] = "E"]

E_0 == /\ pc[0] = "E"
       /\ sem' = [sem EXCEPT ![RightFork(0)] = 1, ![LeftFork(0)] = 1]
       /\ pc'  = [pc EXCEPT ![0] = "L0"]

P0 == L0_0 \/ L1_0 \/ E_0

-----------------------------------------------------------------------------

Next == P0 \/ (\E self \in 1 .. (NP - 1) : P(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1 .. (NP - 1) : SF_vars(P(self))
        /\ SF_vars(P0)

-----------------------------------------------------------------------------

TypeOK == /\ sem \in [Phils -> {0, 1}]
          /\ pc \in [ProcSet -> {"L0", "L1", "E"}]

ExclusiveAccess ==
    \A p \in Phils : ~(pc[p] = "E" /\ pc[(p + 1) % NP] = "E")

NobodyStarves == \A p \in Phils : []<>(pc[p] = "E")

=============================================================================