---------------------------- MODULE GameOfLife ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

Positions == (1..N) \X (1..N)

Neighbors(pos) ==
    LET row == pos[1]
        col == pos[2]
    IN { <<r, c>> : r \in {row-1, row, row+1}, c \in {col-1, col, col+1} }
       \ {pos}

InBoundsNeighbors(pos) ==
    { p \in Neighbors(pos) : p[1] >= 1 /\ p[1] <= N /\ p[2] >= 1 /\ p[2] <= N }

CountLiveNeighbors(pos, g) ==
    Cardinality({ p \in InBoundsNeighbors(pos) : g[p] = 1 })

NextCellState(pos, g) ==
    LET liveCount == CountLiveNeighbors(pos, g)
        currentState == g[pos]
    IN IF currentState = 1
       THEN IF liveCount = 2 \/ liveCount = 3 THEN 1 ELSE 0
       ELSE IF liveCount = 3 THEN 1 ELSE 0

TypeOK ==
    grid \in [Positions -> {0, 1}]

Init ==
    grid \in [Positions -> {0, 1}]

Next ==
    grid' = [pos \in Positions |-> NextCellState(pos, grid)]

Spec == Init /\ [][Next]_grid

=============================================================================