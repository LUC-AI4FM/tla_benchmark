```
MODULE GameOfLife
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES grid

Init ==
  /\ grid \in [1..N -> {<<0, 0>>, <<0, 1>>}]

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
              IF grid[x][y] = <<0, 0>> 
              THEN IF LiveNeighbors(x, y) = 3 
                   THEN <<1, 0>> 
                   ELSE <<0, 0>> 
              ELSE IF LiveNeighbors(x, y) \in {2, 3} 
                   THEN <<1, 0>> 
                   ELSE <<0, 0>>]

LiveNeighbors(x, y) ==
  LET neighbors == {<<x', y'>> : x' \in {x-1, x, x+1}, y' \in {y-1, y, y+1} \ {<<x, y>>}}
      in-bounds == {n \in neighbors : n[1] \in 1..N /\ n[2] \in 1..N}
      liveNeighbors == {n \in in-bounds : grid[n[1]][n[2]] = <<1, 0>>}
  IN Cardinality(liveNeighbors)

Spec ==
  Init /\ [][Next]_grid

THEOREM Spec => []Init
THEOREM Spec => <><>Init
```
Note: The above TLA+ specification models the Game of Life on a finite grid. It uses a function `grid` to represent the state of each cell, where `<<1, 0>>` represents an alive cell and `<<0, 0>>` represents a dead cell. The `Next` action updates the grid according to the standard Game of Life rules. The `LiveNeighbors` operator calculates the number of live neighbors for a given cell. The specification includes the initial condition `Init`, the next-state relation `Next`, and the liveness property `<><>Init`.