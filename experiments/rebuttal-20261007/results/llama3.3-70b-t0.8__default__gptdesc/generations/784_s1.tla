```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Init ==
  /\ grid \in [1..N -> 1..N -> BOOLEAN]

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
             IF (Sum({<<x',y'>} : x' \in (x-1)..(x+1) /\ y' \in (y-1)..(y+1) 
                       /\ (x' # x \/ y' # y) 
                       /\ grid[x'][y'] = TRUE)) = 3
             THEN TRUE
             ELSE IF grid[x][y] = TRUE
                  THEN Sum({<<x',y'>} : x' \in (x-1)..(x+1) /\ y' \in (y-1)..(y+1) 
                            /\ (x' # x \/ y' # y) 
                            /\ grid[x'][y'] = TRUE)) = 2
                  ELSE FALSE]
  /\ UNCHANGED << >>

Spec ==
  Init /\ [][Next]_grid

THEOREM Spec => []Init
```
However, since `Sum` is not defined in the given requirements and TLA+ doesn't natively support a direct sum operator like that for sets, let's rewrite it with proper TLA+ syntax. 

The following revised version correctly defines an operator to calculate the sum of live neighbors.

```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

LiveNeighbors(x, y) ==
  {<<x',y'>} : x' \in (x-1)..(x+1) /\ y' \in (y-1)..(y+1) 
               /\ (x' # x \/ y' # y) 
               /\ (x' >= 1 /\ x' <= N)
               /\ (y' >= 1 /\ y' <= N)
               /\ grid[x'][y'] = TRUE

CountLiveNeighbors(x, y) ==
  Cardinality(LiveNeighbors(x, y))

Init ==
  /\ grid \in [1..N -> 1..N -> BOOLEAN]

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
             IF CountLiveNeighbors(x, y) = 3
             THEN TRUE
             ELSE IF grid[x][y] = TRUE
                  THEN CountLiveNeighbors(x, y) = 2
                  ELSE FALSE]
  /\ UNCHANGED << >>

Spec ==
  Init /\ [][Next]_grid

THEOREM Spec => []Init
```