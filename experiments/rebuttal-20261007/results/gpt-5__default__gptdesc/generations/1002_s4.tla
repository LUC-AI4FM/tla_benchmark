----------------------------- MODULE Barrier -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Proc == 1..N
BStates == {"b0", "b1"}

VARIABLES pc

vars == << pc >>

TypeOK == pc \in [Proc -> BStates]

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
  ( \E p \in Proc: Enter(p) ) \/ Reset

Spec == Init /\ [][Next]_vars

Inv == TypeOK

BarrierProperty ==
  []( \A p \in Proc:
        (pc[p] = "b1" /\ pc'[p] = "b0")
        => (\A q \in Proc: pc[q] = "b1")
     )

============================================================================