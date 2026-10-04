---------------------------- MODULE GameOfLife ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

Pos == (1..N) \X (1..N)

Sum(S, f) == 
    LET RECURSIVE SumHelper(_, _)
        SumHelper(T, acc) == 
            IF T = {} THEN acc
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN SumHelper(T \ {x}, acc + f[x])
    IN SumHelper(S, 0)

CellValue(x, y) == 
    IF x < 1 \/ x > N \/ y < 1 \/ y > N THEN 0
    ELSE IF grid[<<x, y>>] THEN 1 ELSE 0

NeighborCount(x, y) == 
    CellValue(x-1, y-1) + CellValue(x, y-1) + CellValue(x+1, y-1) +
    CellValue(x-1, y) + CellValue(x+1, y) +
    CellValue(x-1, y+1) + CellValue(x, y+1) + CellValue(x+1, y+1)

NextCellState(x, y) == 
    LET count == NeighborCount(x, y)
        alive == grid[<<x, y>>]
    IN IF alive THEN (count = 2 \/ count = 3)
       ELSE (count = 3)

TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |-> NextCellState(p[1], p[2])]

Spec == Init /\ [][Next]_grid

=============================================================================