------------------------------ MODULE TwoProcInc ------------------------------

EXTENDS Naturals

CONSTANTS A, B

VARIABLES x, pc

ProcSet == {A, B}
vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = [A |-> "a1", B |-> "b1"]

A_Step ==
  /\ pc[A] = "a1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![A] = "Done"]

B_Step ==
  /\ pc[B] = "b1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![B] = "Done"]

Terminating ==
  /\ pc[A] = "Done"
  /\ pc[B] = "Done"
  /\ UNCHANGED vars

Next == A_Step \/ B_Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(A_Step) /\ WF_vars(B_Step)

TypeOK ==
  /\ x \in Nat
  /\ pc \in [ProcSet -> {"a1", "b1", "Done"}]

DoneCountOK ==
  x = (IF pc[A] = "Done" THEN 1 ELSE 0)
    + (IF pc[B] = "Done" THEN 1 ELSE 0)

AllDone ==
  /\ pc[A] = "Done"
  /\ pc[B] = "Done"

Termination == <>AllDone

============================================================================