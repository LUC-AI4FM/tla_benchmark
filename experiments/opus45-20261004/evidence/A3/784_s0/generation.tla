---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Pos == (0..(N-1)) \X (0..(N-1))

VARIABLE grid

TypeOK == grid \in [Pos -> BOOLEAN]

RECURSIVE SumSet(_,_)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumSet(f, S \ {x})

Neighbors(x, y) ==
    { <<x + dx, y + dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1} }
    \ { <<x, y>> }

CellValue(pos) ==
    IF pos \in Pos THEN grid[pos] ELSE FALSE

CountLiveNeighbors(x, y) ==
    LET nbrs == Neighbors(x, y)
        valFunc == [p \in nbrs |-> IF CellValue(p) THEN 1 ELSE 0]
    IN SumSet(valFunc, nbrs)

NextCellState(x, y) ==
    LET count == CountLiveNeighbors(x, y)
        alive == grid[<<x, y>>]
    IN IF alive
       THEN count \in {2, 3}
       ELSE count = 3

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [pos \in Pos |-> NextCellState(pos[1], pos[2])]

Spec == Init /\ [][Next]_grid

AllDead == \A pos \in Pos : ~grid[pos]

AllAlive == \A pos \in Pos : grid[pos]

LiveCellCount == Cardinality({pos \in Pos : grid[pos]})

=============================================================================