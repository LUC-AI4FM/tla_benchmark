---------------------------- MODULE GameOfLife ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

\* The set of all board coordinates
Coords == (0..N-1) \X (0..N-1)

\* Helper operator to sum values over a finite set
\* F is a function from elements of S to integers
SumOver(S, F(_)) ==
    LET RECURSIVE SumHelper(_)
        SumHelper(T) ==
            IF T = {} THEN 0
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN F(x) + SumHelper(T \ {x})
    IN SumHelper(S)

\* Returns 1 if the cell at position (x, y) is alive, 0 otherwise
\* Cells outside the board are considered dead
CellValue(x, y) ==
    IF x >= 0 /\ x < N /\ y >= 0 /\ y < N
    THEN IF grid[<<x, y>>] THEN 1 ELSE 0
    ELSE 0

\* The set of neighbor offsets (excluding the cell itself)
NeighborOffsets == {<<dx, dy>> \in (-1..1) \X (-1..1) : <<dx, dy>> /= <<0, 0>>}

\* Count the number of live neighbors for a cell at position (x, y)
CountLiveNeighbors(x, y) ==
    SumOver(NeighborOffsets, LAMBDA offset : CellValue(x + offset[1], y + offset[2]))

\* Compute the next state of a cell based on Conway's Game of Life rules
NextCellState(x, y) ==
    LET neighbors == CountLiveNeighbors(x, y)
        alive == grid[<<x, y>>]
    IN IF alive
       THEN neighbors = 2 \/ neighbors = 3  \* Cell survives if 2 or 3 neighbors
       ELSE neighbors = 3                    \* Dead cell becomes alive if exactly 3 neighbors

\* Type invariant: grid maps each coordinate to a Boolean
TypeOK ==
    grid \in [Coords -> BOOLEAN]

\* Initial condition: any valid grid configuration
Init ==
    grid \in [Coords -> BOOLEAN]

\* Next-state relation: compute the standard Life update for all cells simultaneously
Next ==
    grid' = [pos \in Coords |-> NextCellState(pos[1], pos[2])]

\* Temporal specification with stuttering allowed
Spec == Init /\ [][Next]_grid

=============================================================================