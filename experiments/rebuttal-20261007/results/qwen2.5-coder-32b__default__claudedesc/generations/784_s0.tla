------------------------------- MODULE ConwayGameOfLife -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES grid

Init == grid \in [1..N -> [1..N -> BOOLEAN]]

sc(p) == IF p \notin (1..N) X (1..N) \/ grid[p] = FALSE THEN 0 ELSE 1

score(x, y) == 
    LET neighbors == {(x-1, y-1), (x-1, y), (x-1, y+1),
                      (x, y-1),           (x, y+1),
                      (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN  SUM {sc(n) : n \in neighbors}

Next == 
    /\ grid' \in [1..N -> [1..N -> BOOLEAN]]
    /\ \A x \in 1..N, y \in 1..N :
        LET liveNeighbors == score(x, y)
        IN  grid'[x][y] = (liveNeighbors = 3) \/ (grid[x][y] /\ liveNeighbors = 2)

Spec == Init /\ [][Next]_<<grid>>

TypeOK == grid \in [1..N -> [1..N -> BOOLEAN]]

=============================================================================