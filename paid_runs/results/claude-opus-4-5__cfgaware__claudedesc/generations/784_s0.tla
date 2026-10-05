---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, TLC

CONSTANT N

VARIABLES grid

vars == <<grid>>

Pos == (1..N) \X (1..N)

TypeOK == grid \in [Pos -> BOOLEAN]

sc(p) == IF p[1] >= 1 /\ p[1] <= N /\ p[2] >= 1 /\ p[2] <= N
         THEN IF grid[p] THEN 1 ELSE 0
         ELSE 0

score(p) == sc(<<p[1]-1, p[2]-1>>) + sc(<<p[1]-1, p[2]>>) + sc(<<p[1]-1, p[2]+1>>) +
            sc(<<p[1], p[2]-1>>) + sc(<<p[1], p[2]+1>>) +
            sc(<<p[1]+1, p[2]-1>>) + sc(<<p[1]+1, p[2]>>) + sc(<<p[1]+1, p[2]+1>>)

Init == grid \in [Pos -> BOOLEAN]

NextCell(p) == LET n == score(p)
               IN IF grid[p]
                  THEN n = 2 \/ n = 3
                  ELSE n = 3

Next == grid' = [p \in Pos |-> NextCell(p)]

Spec == Init /\ [][Next]_vars

=============================================================================