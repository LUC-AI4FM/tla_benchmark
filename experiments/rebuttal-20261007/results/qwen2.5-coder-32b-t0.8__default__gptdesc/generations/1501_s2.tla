------------------------------- MODULE FactorialMachine -------------------------------

EXTENDS Naturals

CONSTANTS fact

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x' = fact(3)
       /\ UNCHANGED <<>>
    \/ /\ x' = fact(9)
       /\ UNCHANGED <<>>

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

=============================================================================