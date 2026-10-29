---------------------------- MODULE test59 ----------------------------
EXTENDS Naturals, TLC

VARIABLE y

Init == y = 0

Next == LET x == y + 1
            M == INSTANCE test59a
        IN  y' = (M!xplus1 - 1) % 5

Spec == Init /\ [][Next]_y /\ WF_y(Next)

Invariant == y \in 0..4

Liveness == []<>(y = 4)
=============================================================================