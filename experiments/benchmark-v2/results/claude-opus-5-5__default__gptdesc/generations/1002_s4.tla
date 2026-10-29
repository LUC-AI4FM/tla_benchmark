---------------------------- MODULE Barrier ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

ProcSet == 1..N

VARIABLE pc

vars == << pc >>

-------------------------------------------------------------------------

Init == pc = [p \in ProcSet |-> "b0"]

\* A single process enters the barrier.
b0(self) == /\ pc[self] = "b0"
            /\ pc' = [pc EXCEPT ![self] = "b1"]

\* Once all processes have entered the barrier, all leave it together.
b1 == /\ \A q \in ProcSet : pc[q] = "b1"
      /\ pc' = [p \in ProcSet |-> "b0"]

Next == \/ \E self \in ProcSet : b0(self)
        \/ b1

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------

TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

\* A process cannot leave the barrier while some other process
\* has not yet entered it.
BarrierProperty ==
    [][\A p \in ProcSet :
          (pc[p] = "b1" /\ pc'[p] = "b0")
             => \A q \in ProcSet : pc[q] = "b1"]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
=========================================================================