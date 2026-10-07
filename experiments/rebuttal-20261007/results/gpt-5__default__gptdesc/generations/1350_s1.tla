----------------------------- MODULE CounterToFive -----------------------------
EXTENDS Naturals

VARIABLES x

Init ==
  x = 1

Next ==
  \/ x < 5 /\ x' = x + 1
  \/ x = 5 /\ x' = x

Spec ==
  Init /\ [] [Next]_<<x>> /\ WF_<<x>>(Next)

TypeInv ==
  x \in Nat

RangeInv ==
  x \in 1..5

Liveness ==
  <>[] (x = 5)

THEOREM Spec => []TypeInv /\ []RangeInv /\ Liveness
=============================================================================