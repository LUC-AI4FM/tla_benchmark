------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS TLC, Integers

CONSTANTS 
    \* No constants specified in the description

VARIABLES 
    x

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1, 2, 3, 4, 5}, _ > 1, _ % 2 =/= 0)

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================