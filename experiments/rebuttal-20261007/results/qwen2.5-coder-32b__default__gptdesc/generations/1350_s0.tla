------------------------------- MODULE IncrementToFive -------------------------------
EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES x

Init == x = 1

Next ==
    \/ /\ x < MaxValue
       /\ x' = x + 1
    \/ /\ x = MaxValue
       /\ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
    /\ WF_next(Next)

Inv == x \in 1..MaxValue

Liveness == <>[](x = MaxValue)

THEOREM Spec => []Inv /\ Liveness
=============================================================================