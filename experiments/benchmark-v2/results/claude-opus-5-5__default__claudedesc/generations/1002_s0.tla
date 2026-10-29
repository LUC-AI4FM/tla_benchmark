---------------------------- MODULE CyclicBarrier ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

VARIABLE pc

vars == << pc >>

ProcSet == 1..N

Init == pc = [p \in ProcSet |-> "b0"]

b0(self) == /\ pc[self] = "b0"
            /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 == /\ \A p \in ProcSet : pc[p] = "b1"
      /\ pc' = [p \in ProcSet |-> "b0"]

Next == \/ \E self \in ProcSet : b0(self)
        \/ b1

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

BarrierStep ==
    \A p, q \in ProcSet :
        (pc[p] = "b0" /\ pc[q] = "b1") => (pc'[q] = "b1")

BarrierProperty == [][BarrierStep]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
=============================================================================