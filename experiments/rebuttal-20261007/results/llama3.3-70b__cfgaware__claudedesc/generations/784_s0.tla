---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

sc[p \in (1..N) \times (1..N)] == IF p \in (1..N) \times (1..N) THEN grid[p] ELSE 0

score[p \in (1..N) \times (1..N)] == 
  + sc[(p[1] - 1)%N + 1, p[2]] 
  + sc[(p[1] + 1)%N + 1, p[2]] 
  + sc[p[1], (p[2] - 1)%N + 1] 
  + sc[p[1], (p[2] + 1)%N + 1]
  + sc[(p[1] - 1)%N + 1, (p[2] - 1)%N + 1]
  + sc[(p[1] - 1)%N + 1, (p[2] + 1)%N + 1]
  + sc[(p[1] + 1)%N + 1, (p[2] - 1)%N + 1]
  + sc[(p[1] + 1)%N + 1, (p[2] + 1)%N + 1]

TypeOK == grid \in [((1..N) \times (1..N)) -> BOOLEAN]

Init == TypeOK

Next == 
  \E newGrid \in [((1..N) \times (1..N)) -> BOOLEAN] : 
    newGrid = [p \in ((1..N) \times (1..N)) |-> 
      IF grid[p] 
        THEN score[p] = 2 OR score[p] = 3 
        ELSE score[p] = 3] 
  /\ grid' = newGrid

Spec == Init /\ [][Next]_grid
=============================================================================