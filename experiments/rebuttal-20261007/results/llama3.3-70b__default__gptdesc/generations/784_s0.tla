```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Sum(s, f) == IF s = {} THEN 0 ELSE f[CHOOSE x \in s] + Sum(s \ {CHOOSE x \in s}, f)

IsAlive(x, y) == 
  IF (x < 1) OR (x > N) OR (y < 1) OR (y > N)
  THEN FALSE
  ELSE grid[x][y]

LiveNeighbors(x, y) == 
  Sum(
    {<<x-1, y-1>, <x, y-1>, <x+1, y-1>,
      <x-1, y>,             <x+1, y>,
      <x-1, y+1>, <x, y+1>, <x+1, y+1>},
    [p |-> IsAlive(p[1], p[2])]
  )

Next == 
  \E grid' \in [1..N -> [1..N -> BOOLEAN]]:
    \A x \in 1..N:
      \A y \in 1..N:
        grid'[x][y] = 
          IF IsAlive(x, y)
          THEN (LiveNeighbors(x, y) = 2 OR LiveNeighbors(x, y) = 3)
          ELSE LiveNeighbors(x, y) = 3

Init == 
  \A x \in 1..N: 
    \A y \in 1..N:
      grid[x][y] = FALSE

Spec == Init /\ [][Next]_grid

THEOREM Spec => []Init
```