----------------------------- MODULE GameOfLife -----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES grid

Pos == (0..(N-1)) \X (0..(N-1))

Sum(S, f) ==
    LET RECURSIVE SumHelper(_, _)
        SumHelper(T, acc) ==
            IF T = {} THEN acc
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN SumHelper(T \ {x}, acc + f[x])
    IN SumHelper(S, 0)

Neighbors(x, y) ==
    { <<x + dx, y + dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1} }
    \ { <<x, y>> }

CellValue(pos) ==
    IF pos \in Pos THEN grid[pos] ELSE FALSE

LiveNeighborCount(x, y) ==
    LET neighborSet == Neighbors(x, y)
        f == [p \in neighborSet |-> IF CellValue(p) THEN 1 ELSE 0]
    IN Sum(neighborSet, f)

NextCellState(x, y) ==
    LET count == LiveNeighborCount(x, y)
        alive == grid[<<x, y>>]
    IN IF alive
       THEN count \in {2, 3}
       ELSE count = 3

TypeOK ==
    grid \in [Pos -> BOOLEAN]

Init ==
    grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [pos \in Pos |-> NextCellState(pos[1], pos[2])]

Spec == Init /\ [][Next]_grid

=============================================================================