----------------------------- MODULE IncrementToFive -----------------------------

EXTENDS Naturals

CONSTANTS Max

VARIABLES x

Init == x = 1

Next ==
  ((x < Max) /\ x' = x + 1)
  \/ ((x = Max) /\ x' = x)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

TypeInv == x \in 1..Max

Liveness == <>[] (x = Max)

ASSUME Max = 5

THEOREM Spec => [](TypeInv)

THEOREM Spec => Liveness

=============================================================================