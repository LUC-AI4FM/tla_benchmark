------------------------------- MODULE ConjunctiveInit -------------------------------

VARIABLES x, y

CONSTANTS Init, Next, Spec, State

Init == /\ y = 0
        /\ x = 0
        /\ y = x

Next == TRUE

Spec == Init /\ [][Next]_<<x, y>>

State == <<x, y>>

=============================================================================