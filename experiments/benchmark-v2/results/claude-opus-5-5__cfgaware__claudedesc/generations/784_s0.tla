---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N

VARIABLE grid

vars == << grid >>

Pos == (1..N) \X (1..N)

TypeOK == grid \in [Pos -> BOOLEAN]

sc(x, y) == IF x \in 1..N /\ y \in 1..N /\ grid[<<x, y>>] THEN 1 ELSE 0

score(p) ==
    LET x == p[1]
        y == p[2]
    IN  sc(x - 1, y - 1) + sc(x, y - 1) + sc(x + 1, y - 1)
      + sc(x - 1, y)                    + sc(x + 1, y)
      + sc(x - 1, y + 1) + sc(x, y + 1) + sc(x + 1, y + 1)

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |->
                    \/ /\ grid[p]
                       /\ score(p) \in {2, 3}
                    \/ /\ ~grid[p]
                       /\ score(p) = 3]

Spec == Init /\ [][Next]_vars

====