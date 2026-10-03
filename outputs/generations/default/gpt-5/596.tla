------------------------------ MODULE OneVarFair ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS CexTrace

ASSUME CexTrace = << [x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2], [x |-> 0] >>

VARIABLES x

Init ==
  x = 0

Next ==
  \/ /\ x = 0
     /\ x' \in {1, 2}
  \/ /\ x \in {1, 2}
     /\ x' = 0

Spec ==
  Init /\ [][Next]_x /\ WF_x(Next)

TypeInv ==
  x \in {0, 1, 2}

EventuallyReturnZero ==
  []<>(x = 0)

Avoid1Eventually ==
  <>[](x # 1)

Avoid2Eventually ==
  <>[](x # 2)

AvoidEitherEventually ==
  Avoid1Eventually \/ Avoid2Eventually

NotAvoidEitherEventually ==
  ~AvoidEitherEventually

StepOK(s, t) ==
  IF s.x = 0 THEN t.x \in {1, 2} ELSE t.x = 0

Postcondition ==
  LET T == CexTrace IN
    /\ Len(T) = 5
    /\ T[1] = [x |-> 0]
    /\ \A i \in 1..(Len(T) - 1): StepOK(T[i], T[i + 1])
    /\ { T[2], T[4] } = { [x |-> 1], [x |-> 2] }

=============================================================================