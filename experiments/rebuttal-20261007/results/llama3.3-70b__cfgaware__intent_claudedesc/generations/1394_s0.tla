```
MODULE Main
VARIABLES x, y
CONSTANT c

c == 5

Instance == INSTANCE SubModule WITH v <- c

Spec == Instance!Spec

======================================

MODULE SubModule
VARIABLES u, v, w

Init == (u \in {1, 2, 3}) /\ (v = 0) /\ (w \in {1, 2})

Next == u' = u + 1 /\ UNCHANGED <<v, w>>

Spec == Init /\ [][Next]_<<u, v, w>>
```