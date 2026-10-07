------------------------------- MODULE F -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1, 2, 3, 4, 5}, (s) -> s > 1, (s, b) -> s % 2 # 0 /\ b)

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================