------------------------------- MODULE ConwayGameOfLife -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES grid

GridCell == [x \in 1..N, y \in 1..N -> BOOLEAN]

Init == 
    /\ grid \in GridCell

Next ==
    LET liveNeighbors[x \in 1..N, y \in 1..N] ==
            (Cardinality({<dx, dy> \in {-1..1} \X {-1..1} :
                dx # 0 \/ dy # 0 /\
                x + dx \in 1..N /\ y + dy \in 1..N /\
                grid[x + dx][y + dy]}))
    IN
        /\ grid' = [x \in 1..N, y \in 1..N -> 
            \/ (grid[x][y] /\ liveNeighbors[x][y] \in {2, 3})
            \/ (\neg grid[x][y] /\ liveNeighbors[x][y] = 3)]

Spec ==
    Init /\ [][Next]_<<grid>>

=============================================================================