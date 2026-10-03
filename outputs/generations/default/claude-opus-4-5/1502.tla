---------------------------- MODULE SmallStateMachine ----------------------------
EXTENDS Integers

CONSTANTS Op(_)

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

SubsetHelper == {y \in Op(x) : y >= 0}

FilteredOp(v) == {z \in Op(v) : z # v}

TypeInvariant == x \in Int

=============================================================================