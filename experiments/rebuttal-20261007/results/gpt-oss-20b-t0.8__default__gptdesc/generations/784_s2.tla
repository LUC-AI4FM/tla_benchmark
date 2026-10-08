MODULE Life
EXTENDS TLC

CONSTANT N

VARIABLE grid

Board == 1 .. N \X 1 .. N

IntOfBool(b) ==
  IF b THEN 1 ELSE 0

Neighbors(cell) ==
  {p \in Board :
    Abs(p[1] - cell[1]) <= 1 /\ Abs(p[2] - cell[2]) <= 1 /\ ~(p = cell)}

CountLiveNeighbors(cell) ==
  \sum p \in Neighbors(cell) : IntOfBool(grid[p])

NextUpdate ==
  grid' =
    [cell \in Board |-> IF grid[cell]
                          THEN (CountLiveNeighbors(cell)=2 \/ CountLiveNeighbors(cell)=3)
                          ELSE (CountLiveNeighbors(cell)=3)]

Stutter == grid' = grid

NextStep == NextUpdate \/ Stutter

Init ==
  /\ N >= 1
  /\ grid \in [Board -> BOOLEAN]

Spec == Init /\ []NextStep