---------------------------- MODULE Barrier ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES pc

vars == << pc >>

ProcSet == 1..N

Init == pc = [p \in ProcSet |-> "b0"]

Enter(self) ==
    /\ pc[self] = "b0"
    /\ pc' = [pc EXCEPT ![self] = "b1"]

Release ==
    /\ \A p \in ProcSet : pc[p] = "b1"
    /\ pc' = [p \in ProcSet |-> "b0"]

Next ==
    \/ \E self \in ProcSet : Enter(self)
    \/ Release

Spec == Init /\ [][Next]_vars

TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

BarrierProperty ==
    [][\A p \in ProcSet :
          (pc[p] = "b1" /\ pc'[p] = "b0") =>
              \A q \in ProcSet : pc[q] = "b1"]_vars

=============================================================================