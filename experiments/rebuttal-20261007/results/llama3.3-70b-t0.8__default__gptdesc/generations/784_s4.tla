```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES grid

Init == (grid = [i \in 1..N, j \in 1..N |-> FALSE])

Sum(s, f) == IF s = {} THEN 0 ELSE f(Head(s)) + Sum(Tail(s), f)

IsAlive(i, j) == 
  IF (i < 1) OR (i > N) OR (j < 1) OR (j > N) 
  THEN FALSE 
  ELSE grid[i, j]

LiveNeighbors(i, j) == 
  Sum(
    {[x, y] : x \in {i-1, i, i+1}, y \in {j-1, j, j+1}} \ {i, j},
    [z |-> IF IsAlive(z[1], z[2]) THEN 1 ELSE 0]
  )

Next == 
  grid' = [i \in 1..N, j \in 1..N |-> 
            IF IsAlive(i, j) 
            THEN (LiveNeighbors(i, j) = 2) OR (LiveNeighbors(i, j) = 3)
            ELSE LiveNeighbors(i, j) = 3]

Spec == Init /\ [][Next]_grid

THEOREM Spec => []Init
```