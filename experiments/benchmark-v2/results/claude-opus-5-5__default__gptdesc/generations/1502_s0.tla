---------------------------- MODULE OpStateMachine ----------------------------
EXTENDS Naturals

CONSTANT Op(_)

VARIABLE x

vars == << x >>

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_vars

PowerOf(S) == SUBSET S

InPowerOf(T, S) == T \in SUBSET S

================================================================================