---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE grid

TypeOK == grid \in [1..N -> BOOLEAN]

Spec == 
  /\ grid' \in [1..N -> BOOLEAN]
  /\ TypeOK
  /\ WF_Vars({grid})

Next ==
  /\ grid' = [x \in 1..N |-> IF grid[x] THEN (NeighborCount(x) = 2 \/ NeighborCount(x) = 3) ELSE NeighborCount(x) = 3]

NeighborCount(self) == 
  LET neighbors == { (self[1] + dx) % N + 1 @ (self[2] + dy) % N + 1 : dx \in {-1,0,1}, dy \in {-1,0,1} \ {0,0} }
  IN \A n \in neighbors : grid[n]

Init == 
  /\ TypeOK

THEOREM Spec => []TypeOK
THEOREM Spec => <><>~(grid = grid')
=============================================================================