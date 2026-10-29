---------------------------- MODULE test59 ----------------------------
EXTENDS Naturals

VARIABLE y

Init == y = 0

Next == LET x == y + 1
            M == INSTANCE test59a
        IN  y' = (M!xplus1 - 1) % 5

Spec == Init /\ [][Next]_y /\ WF_y(Next)

TypeInvariant == y \in 0..4

Invariant == y \in 0..4

Liveness == []<>(y = 4)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=======================================================================