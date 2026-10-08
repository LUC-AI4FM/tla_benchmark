---------------------------- MODULE SmallStateMachine ----------------------------
EXTENDS Naturals

CONSTANTS fact

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x' = fact(3)
       /\ UNCHANGED <<x>>
    \/ /\ x' = fact(9)
       /\ UNCHANGED <<x>>

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
=============================================================================