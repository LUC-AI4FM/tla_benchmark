---------------------------- MODULE ConstantState ----------------------------
EXTENDS Integers

CONSTANT State

VARIABLE state

Init == (state = 0)

Next == state' = state

Spec == Init /\ [][Next]_state

THEOREM Spec => []Init
THEOREM Spec => [](state = 0)
=============================================================================