---------------------------- MODULE OpStateMachine ----------------------------
EXTENDS Naturals

CONSTANT Op(_)

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper operators involving a subset expression *)

Subsets(S) == SUBSET S

Successors == Subsets(Op(x))

=============================================================================