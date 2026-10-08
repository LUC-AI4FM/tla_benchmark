```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Init ==
  /\ grid \in [1..N -> 1..N -> BOOLEAN]

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
               IF AliveNeighbors(x, y) = 2 THEN grid[x][y]
               ELSE IF AliveNeighbors(x, y) = 3 THEN TRUE
               ELSE FALSE]
  /\ UNCHANGED << >>

AliveNeighbors(x, y) ==
  LET neighbors == {<<x', y'> | x' \in (x-1)..(x+1) /\ y' \in (y-1)..(y+1) 
                    /\ (x' # x \/ y' # y) /\ x' \in 1..N /\ y' \in 1..N}
  IN Sum({grid[x'][y'] |<<x', y'>| \in neighbors})

Sum(S) == IF S = {} THEN 0 ELSE 
           LET s == CHOOSE s \in S : TRUE
           IN s + Sum(S \ {s})

Spec ==
  /\ Init
  /\ [][Next]_grid

THEOREM Spec => []Init
```