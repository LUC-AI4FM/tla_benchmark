------------------------------- MODULE SmallStateMachine -------------------------------

VARIABLES x

CONSTANTS
    \* No additional constants needed for this specification

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1, 2, 3, 4, 5}, (s \in {1, 2, 3, 4, 5} => s > 1), (s \in {1, 2, 3, 4, 5} => s % 2 = 1))

Next == UNCHANGED x

=============================================================================