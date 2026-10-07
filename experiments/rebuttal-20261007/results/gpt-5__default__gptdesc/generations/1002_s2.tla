----------------------------- MODULE Barrier -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

CONSTANT Proc
ASSUME Proc = 1..N

VARIABLES pc

BStates == {"b0", "b1"}

TypeOK ==
  pc \in [Proc -> BStates]

Init ==
  pc = [p \in Proc |-> "b0"]

Enter(p) ==
  /\ p \in Proc
  /\ pc[p] = "b0"
  /\ pc' = [pc EXCEPT ![p] = "b1"]

AllInB1 ==
  \A p \in Proc: pc[p] = "b1"

Reset ==
  /\ AllInB1
  /\ pc' = [p \in Proc |-> "b0"]

Next ==
  \/ \E p \in Proc: Enter(p)
  \/ Reset

Spec ==
  Init /\ [][Next]_pc

Leave(p) ==
  /\ p \in Proc
  /\ pc[p] = "b1" /\ pc'[p] = "b0"

BarrierProperty ==
  []( ( \E p \in Proc: Leave(p) ) => AllInB1 )

Invariant ==
  TypeOK

============================================================================