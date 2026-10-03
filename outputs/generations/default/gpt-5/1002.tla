----------------------------- MODULE Barrier -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Proc == 1..N

VARIABLES pc

vars == << pc >>

TypeOK == pc \in [Proc -> {"b0", "b1"}]

Init == pc = [p \in Proc |-> "b0"]

AllInB1 == \A p \in Proc: pc[p] = "b1"

Enter(p) ==
  /\ p \in Proc
  /\ pc[p] = "b0"
  /\ pc' = [pc EXCEPT ![p] = "b1"]

Reset ==
  /\ AllInB1
  /\ pc' = [p \in Proc |-> "b0"]

Next ==
  \/ Reset
  \/ \E p \in Proc: Enter(p)

Spec == Init /\ [][Next]_vars

TypeInvariant == []TypeOK

NoEarlyLeave ==
  []((\E p \in Proc: pc[p] = "b1" /\ pc'[p] = "b0") => (\A q \in Proc: pc[q] = "b1"))
=============================================================================