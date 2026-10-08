------------------------------ MODULE RingCopy ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y, pc

Proc == 0..(N - 1)
Labels == {"a", "b", "Done"}

Init ==
  /\ x = [i \in Proc |-> 0]
  /\ y = [i \in Proc |-> 0]
  /\ pc = [i \in Proc |-> "a"]

vars == << x, y, pc >>

Neighbor(i) == IF i = 0 THEN N - 1 ELSE i - 1

A(i) ==
  /\ pc[i] = "a"
  /\ x' = [x EXCEPT ![i] = 1]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "b"]

B(i) ==
  /\ pc[i] = "b"
  /\ x' = x
  /\ y' = [y EXCEPT ![i] = x[Neighbor(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Next == \E i \in Proc: A(i) \/ B(i)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \in [Proc -> {0, 1}]
  /\ y \in [Proc -> {0, 1}]
  /\ pc \in [Proc -> Labels]

XAfterA ==
  \A i \in Proc: (pc[i] \in {"b", "Done"}) => x[i] = 1

SomeNotDoneOrY1 ==
  (\E i \in Proc: pc[i] # "Done") \/ (\E i \in Proc: y[i] = 1)

Inv == TypeOK /\ XAfterA /\ SomeNotDoneOrY1

PCorrect ==
  (\A i \in Proc: pc[i] = "Done") => (\E i \in Proc: y[i] = 1)

THEOREM InvImpliesPCorrect == Inv => PCorrect
PROOF OBVIOUS

THEOREM InvIsInvariant == Spec => []Inv
PROOF OMITTED

THEOREM Correctness ==
  Spec => []PCorrect
PROOF OBVIOUS
QED

THEOREM Correctness2 ==
  Init /\ [][Next]_vars => []PCorrect
PROOF OMITTED

============================================================================