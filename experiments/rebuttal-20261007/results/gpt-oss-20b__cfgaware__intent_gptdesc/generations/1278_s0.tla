------------------------------ MODULE DigitSM ------------------------------
EXTENDS Naturals

VARIABLE state

Even(x) == x % 2 = 0

Init == state = 0

Safety == state \in 0 .. 9 /\ Even(state)

Next == state' \in 0 .. 9 /\ Even(state')

Spec == Init /\ [][Next]_state

Inv == Safety

THEOREM Spec => []Inv
=============================================================================