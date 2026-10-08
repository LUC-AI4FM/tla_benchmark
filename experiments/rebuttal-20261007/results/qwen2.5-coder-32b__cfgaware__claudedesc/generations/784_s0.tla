------------------------------- MODULE GameOfLife -------------------------------

CONSTANTS N \* Assumed to be 4 in the model-checking configuration

VARIABLE grid

Init == /\ grid \in [1..N -> [1..N -> BOOLEAN]]

sc(p) == IF p \notin (1..N) \/ p \notin (1..N) \/ ~grid[p[1]][p[2]] THEN 0 ELSE 1

score(x, y) == 
    LET neighbors == {(x-1, y-1), (x-1, y), (x-1, y+1),
                      (x, y-1),           (x, y+1),
                      (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN  \Sum p \in neighbors : sc(p)

Next == 
    /\ \E newGrid \in [1..N -> [1..N -> BOOLEAN]] :
        /\ \A x \in 1..N, y \in 1..N :
            LET liveNeighbors == score(x, y)
            IN  (grid[x][y] = TRUE /\ liveNeighbors \in {2, 3}) \/ 
                (grid[x][y] = FALSE /\ liveNeighbors = 3) =>
                    newGrid[x][y] = TRUE
                ELSE
                    newGrid[x][y] = FALSE
        /\ grid' = newGrid

TypeOK == grid \in [1..N -> [1..N -> BOOLEAN]]

Spec == Init /\ []<>(Next)

===============================================================================