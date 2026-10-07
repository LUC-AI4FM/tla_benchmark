----------------------------- MODULE Barrier -----------------------------

EXTENDS Naturals, Integers

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES pc

Proc == 1..N
PCVals == {"b0", "b1"}

TypeOK == pc \in [Proc -> PCVals]

Init == pc = [i \in Proc |-> "b0"]

AllB1 == \A i \in Proc: pc[i] = "b1"

Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "b0"
  /\ pc' = [pc EXCEPT ![i] = "b1"]

Reset ==
  /\ AllB1
  /\ pc' = [i \in Proc |-> "b0"]

Next ==
  \/ Reset
  \/ \E i \in Proc: Enter(i)

vars == << pc >>

Spec == Init /\ [][Next]_vars

TypeInvariant == []TypeOK

Leave(i) == pc[i] = "b1" /\ pc'[i] = "b0"

BarrierProperty == [](\A i \in Proc: Leave(i) => \A j \in Proc \ {i}: pc[j] = "b1")

=============================================================================