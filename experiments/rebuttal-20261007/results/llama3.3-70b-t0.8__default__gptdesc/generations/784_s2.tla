```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Sum(s, f) == IF s = {} THEN 0 ELSE f[CHOOSE x \in s] + Sum(s \ {CHOOSE x \in s}, f)

IsAlive(x, y) ==
  IF (x \in 1..N) /\ (y \in 1..N)
  THEN grid[x][y]
  ELSE FALSE

LiveNeighbors(x, y) ==
  Sum(
    {x-1, x, x+1} \intersect 1..N
    \X
    {y-1, y, y+1} \intersect 1..N,
    LAMBDA <<i, j>> : IsAlive(i, j)
  ) - IF (x \in 1..N) /\ (y \in 1..N) THEN grid[x][y] ELSE 0

Init ==
  /\ grid = [x \in 1..N, y \in 1..N |-> FALSE]

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
              IF IsAlive(x, y)
              THEN (LiveNeighbors(x, y) = 2) OR (LiveNeighbors(x, y) = 3)
              ELSE LiveNeighbors(x, y) = 3]
  /\ UNCHANGED << >>

Spec ==
  Init /\ [][Next]_grid

THEOREM Spec => []Init
```