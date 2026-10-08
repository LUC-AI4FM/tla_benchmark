------------------- MODULE IncrementUntilFive -------------------
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next ==
    \/ (x < 5 /\ x' = x + 1)
    \/ (x = 5 /\ x' = x)

Spec == Init /\ [][Next]_x /\ WF(Next)

SafetyInvariant == x ∈ 1..5
LivenessProp == <> (x = 5 /\ [](x = 5))