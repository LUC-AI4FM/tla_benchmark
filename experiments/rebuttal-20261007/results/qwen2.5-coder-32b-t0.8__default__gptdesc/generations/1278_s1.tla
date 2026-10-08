------------------------------- MODULE TemporalSystem -------------------------------

EXTENDS TLC, Integers

CONSTANTS
    \* No constants defined in this example

VARIABLES s

F(var) == var \in 0..9 /\ var % 2 = 0

Init == s = 0

Next == F(s')

Spec ==
    /\ Init
    /\ [][Next]_<<s>>
    /\ [](F(s'))

=============================================================================