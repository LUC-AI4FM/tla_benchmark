```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Sum(s, f) == 
  IF s = {} THEN 0 
  ELSE LET x == CHOOSE x \in s IN f(x) + Sum(s \ {x}, f)

IsAlive(p) == 
  IF (p[1] \in 1..N) /\ (p[2] \in 1..N) THEN grid[p]
  ELSE FALSE

LiveNeighbors(p) == 
  LET neighbors == {<<x, y>> \in {<<i, j>> \in [1..N] \times [1..N]: i \in {p[1]-1, p[1], p[1]+1} /\ j \in {p[2]-1, p[2], p[2]+1}}: (x # p[1]) \/ (y # p[2])}
  IN Sum(neighbors, IsAlive)

Init == 
  grid = [p \in [1..N] \times [1..N] |-> FALSE]

Next == 
  \E newGrid \in [grid] : 
    newGrid = [p \in [1..N] \times [1..N] |-> 
      IF IsAlive(<<p[1], p[2]>>) THEN (LiveNeighbors(<<p[1], p[2]>>) = 2) \/ (LiveNeighbors(<<p[1], p[2]>>) = 3)
      ELSE LiveNeighbors(<<p[1], p[2]>>) = 3]
    /\ grid' = newGrid

Spec == Init /\ [][Next]_grid
```