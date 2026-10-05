---------------------------- MODULE SmallStateMachine ----------------------------

EXTENDS Naturals

CONSTANTS Op(_)

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

SubsetHelper(S) == {s \in S : s \subseteq S}

FilterHelper(S, P(_)) == {s \in S : P(s)}

=============================================================================