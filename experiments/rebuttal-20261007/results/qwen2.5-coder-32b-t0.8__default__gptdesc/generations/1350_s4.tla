------------------------------- MODULE IncrementToFive ------------------------------

EXTENDS Naturals

CONSTANTS InitVal, MaxVal

VARIABLES x

Init == x = InitVal

Next ==
    \/ /\ x < MaxVal
       /\ x' = x + 1
    \/ /\ x = MaxVal
       /\ x' = x

Spec ==
    \E init \in {InitVal} :
        /\ x = init
        /\ [][Next]_<<x>>
        /\ WF_next(Next)

\* Liveness property: Eventually reach and remain at MaxVal
<>[](x = MaxVal)

=============================================================================