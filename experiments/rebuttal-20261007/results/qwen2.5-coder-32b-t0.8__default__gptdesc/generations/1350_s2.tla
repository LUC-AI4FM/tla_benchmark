---- MODULE IncrementUntilFive ----

EXTENDS Naturals, TLC

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
    /\ WF_x(Next)

Termination ==
    <>[] (x = MaxValue)

====