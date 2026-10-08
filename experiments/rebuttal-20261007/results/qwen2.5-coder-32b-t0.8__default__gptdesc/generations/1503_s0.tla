----------------------------- MODULE SmallStateMachine -----------------------------

EXTENDS Integers

CONSTANTS 
    Op

VARIABLES x

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1, 2, 3, 4, 5}, (s \in Nat => s > 1), (s, b) \in [Nat -> BOOLEAN] => b = (s % 2 # 0))

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================