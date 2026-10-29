---------------------------- MODULE SmallOpMachine ----------------------------
EXTENDS Naturals

CONSTANT Op(_)

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' \in Op(x)

\* Helper operators involving a subset expression
Subsets == SUBSET Op(x)

NextViaSubset == \E S \in SUBSET Op(x) : x' \in S

Spec == Init /\ [][Next]_vars

=============================================================================