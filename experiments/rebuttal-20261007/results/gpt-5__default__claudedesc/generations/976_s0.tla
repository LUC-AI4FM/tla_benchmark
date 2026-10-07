----------------------------- MODULE RingCopy -----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME N \in Nat \ {0} \cup {0} \land N > 0

VARIABLES x, y, pc

ProcSet == 0..(N-1)

Left(i) == IF i = 0 THEN N-1 ELSE i-1

TypeOK ==
  /\ x \in [ProcSet -> {0,1}]
  /\ y \in [ProcSet -> {0,1}]
  /\ pc \in [ProcSet -> {"a","b","Done"}]

Init ==
  /\ x = [i \in ProcSet |-> 0]
  /\ y = [i \in ProcSet |-> 0]
  /\ pc = [i \in ProcSet |-> "a"]

A(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "a"
  /\ x' = [x EXCEPT ![i] = 1]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "b"]

B(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "b"
  /\ x' = x
  /\ y' = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Next ==
  \E i \in ProcSet:
    A(i) \/ B(i)

vars == << x, y, pc >>

Spec == Init /\ [][Next]_vars

Terminated == \A i \in ProcSet: pc[i] = "Done"

PCorrect == Terminated => (\E i \in ProcSet: y[i] = 1)

Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet: (pc[i] \in {"b","Done"}) => x[i] = 1
  /\ (~Terminated) \/ (\E i \in ProcSet: y[i] = 1)

THEOREM InitImpliesInv == Init => Inv
PROOF OBVIOUS

THEOREM InvIsInductive == Inv /\ Next => Inv'
PROOF OBVIOUS

THEOREM InvInvariant == Spec => []Inv
PROOF OBVIOUS

THEOREM Correctness == Spec => []PCorrect
PROOF OBVIOUS

THEOREM Correctness2 == Spec => []PCorrect
PROOF OBVIOUS
=============================================================================