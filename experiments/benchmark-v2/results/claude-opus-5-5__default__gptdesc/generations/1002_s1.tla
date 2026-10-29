------------------------------- MODULE Barrier -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

ProcSet == 1..N

VARIABLE pc

vars == << pc >>

TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

Init == pc = [p \in ProcSet |-> "b0"]

\* A single process enters the barrier.
Enter(p) == /\ pc[p] = "b0"
            /\ pc' = [pc EXCEPT ![p] = "b1"]

\* Once every process is in the barrier, all are released simultaneously.
Release == /\ \A p \in ProcSet : pc[p] = "b1"
           /\ pc' = [p \in ProcSet |-> "b0"]

Next == \/ \E p \in ProcSet : Enter(p)
        \/ Release

Spec == Init /\ [][Next]_vars

\* No process may leave the barrier (go from "b1" to "b0") while some
\* other process has not yet entered it (is still in "b0").
BarrierProperty ==
    [][ \A p \in ProcSet :
          (pc[p] = "b1" /\ pc'[p] = "b0") => \A q \in ProcSet : pc[q] = "b1"
      ]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
=============================================================================