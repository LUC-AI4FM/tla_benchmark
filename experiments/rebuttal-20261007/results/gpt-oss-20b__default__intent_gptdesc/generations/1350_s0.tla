MODULE Counter
EXTENDS Naturals, Fairness

VARIABLE c

vars == <<c>>

Init == c = 1

Increment == (c < 5 /\ c' = c + 1)
StayAtFive == (c = 5 /\ c' = c)

Next == Increment \/ StayAtFive

Spec == Init /\ [][Next]_vars /\ Fairness(Increment)

Safety == [] ((c < 5 /\ c' = c + 1) \/ (c = 5 /\ c' = c))

BoundInv == [] (c >= 1 /\ c <= 5)

MonotonicityInv == \A c, c': (Next => c' >= c)

Liveness == <>[] (c = 5)