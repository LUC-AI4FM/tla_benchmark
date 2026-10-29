------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == 0 .. (N - 1)

\* Fork indices for philosopher p
RightFork(p) == p
LeftFork(p)  == (p - 1 + N) % N

Init == /\ sem = [i \in 0 .. (N - 1) |-> 1]
        /\ pc  = [self \in ProcSet |-> IF self = 0 THEN "l01" ELSE "l1"]

-------------------------------------------------------------------------------------
\* Philosophers 1 .. N-1 : acquire right fork (self), then left fork ((self-1) mod N)

l1(self) == /\ pc[self] = "l1"
            /\ sem[RightFork(self)] = 1
            /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "l2"]

l2(self) == /\ pc[self] = "l2"
            /\ sem[LeftFork(self)] = 1
            /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "e"]

e(self)  == /\ pc[self] = "e"
            /\ TRUE   \* eat
            /\ pc'  = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED sem

r1(self) == /\ pc[self] = "r1"
            /\ sem' = [sem EXCEPT ![RightFork(self)] = 1]
            /\ pc'  = [pc EXCEPT ![self] = "r2"]

r2(self) == /\ pc[self] = "r2"
            /\ sem' = [sem EXCEPT ![LeftFork(self)] = 1]
            /\ pc'  = [pc EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ e(self) \/ r1(self) \/ r2(self)

-------------------------------------------------------------------------------------
\* Philosopher 0 : acquire left fork (N-1) first, then right fork (0)

l01 == /\ pc[0] = "l01"
       /\ sem[N - 1] = 1
       /\ sem' = [sem EXCEPT ![N - 1] = 0]
       /\ pc'  = [pc EXCEPT ![0] = "l02"]

l02 == /\ pc[0] = "l02"
       /\ sem[0] = 1
       /\ sem' = [sem EXCEPT ![0] = 0]
       /\ pc'  = [pc EXCEPT ![0] = "e0"]

e0  == /\ pc[0] = "e0"
       /\ TRUE   \* eat
       /\ pc'  = [pc EXCEPT ![0] = "r01"]
       /\ UNCHANGED sem

r01 == /\ pc[0] = "r01"
       /\ sem' = [sem EXCEPT ![N - 1] = 1]
       /\ pc'  = [pc EXCEPT ![0] = "r02"]

r02 == /\ pc[0] = "r02"
       /\ sem' = [sem EXCEPT ![0] = 1]
       /\ pc'  = [pc EXCEPT ![0] = "l01"]

Proc0 == l01 \/ l02 \/ e0 \/ r01 \/ r02

-------------------------------------------------------------------------------------

Next == \/ Proc0
        \/ (\E self \in 1 .. (N - 1) : Proc(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ SF_vars(Proc0)
        /\ \A self \in 1 .. (N - 1) : SF_vars(Proc(self))

-------------------------------------------------------------------------------------

TypeOK == /\ sem \in [0 .. (N - 1) -> {0, 1}]
          /\ pc \in [ProcSet -> {"l1", "l2", "e", "r1", "r2",
                                 "l01", "l02", "e0", "r01", "r02"}]

Eating(p) == pc[p] \in {"e", "e0"}

\* No two adjacent philosophers eat at the same time
Invariant == \A p \in ProcSet :
                 (p # (p + 1) % N) => ~(Eating(p) /\ Eating((p + 1) % N))

\* Every philosopher eats infinitely often
StarvationFree == \A p \in ProcSet : []<>Eating(p)

=====================================================================================