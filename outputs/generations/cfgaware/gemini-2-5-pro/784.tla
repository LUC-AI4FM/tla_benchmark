---- MODULE Life ----
EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES grid

\* The set of all coordinates on the N x N board.
Coords == (1..N) \X (1..N)

\* The type invariant, ensuring the grid is a function from coordinates to booleans.
TypeOK == grid \in [Coords -> BOOLEAN]

\* A recursive operator to sum the values of a function F over a finite set S.
RECURSIVE Sum(_, _)
Sum(S, F) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN F[x] + Sum(S \ {x}, F)

\* Returns the state of a cell. Cells outside the board are considered dead (FALSE).
GetCell(g, i, j) ==
    IF <<i, j>> \in DOMAIN g
    THEN g[<<i, j>>]
    ELSE FALSE

\* The set of 8 relative offsets for the neighbors of a cell.
Offsets == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> /= <<0, 0>>}

\* Counts the number of live neighbors for a cell at coordinate c.
LiveNeighbors(g, c) ==
    Sum(Offsets, LAMBDA off : IF GetCell(g, c[1] + off[1], c[2] + off[2]) THEN 1 ELSE 0)

\* The initial state can be any valid grid configuration.
Init == grid \in [Coords -> BOOLEAN]

\* The next-state relation, which computes the next generation of the grid
\* based on the standard rules of Conway's Game of Life.
\* 1. A live cell with < 2 live neighbors dies (underpopulation).
\* 2. A live cell with 2 or 3 live neighbors lives on to the next generation.
\* 3. A live cell with > 3 live neighbors dies (overpopulation).
\* 4. A dead cell with exactly 3 live neighbors becomes a live cell (reproduction).
Next ==
    grid' = [c \in Coords |->
                LET isAlive == grid[c]
                    neighbors == LiveNeighbors(grid, c)
                IN (isAlive /\ neighbors \in {2, 3}) \/ (~isAlive /\ neighbors = 3)]

\* The complete specification, allowing stuttering steps.
Spec == Init /\ [][Next]_<<grid>>

=============================================================================