```
MODULE Main
EXTENDS Integers
CONSTANTS c
VARIABLES x, y

Instance == INSTANCE Second WITH v <- c

Init == (x \in 1..5) /\ (y = 0)

Next == Instance!Next

Spec == Init /\ [][Next]_<<x, y>>

THEOREM Spec => [](~(x = 0))
=====================================

MODULE Second
VARIABLES u, v, w

Init == (u \in 1..5) /\ (v = 0) /\ (w \in {0, 1})

Next == u' = u + 1 /\ UNCHANGED <<v, w>>
```