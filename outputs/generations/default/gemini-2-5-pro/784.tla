---- MODULE Life ----
EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat /\ N > 0

VARIABLES grid

vars == <<grid>>

BoardCoords == (1..N) \X (1..N)

\* A recursive operator to sum the values of a function f over a finite set S.
RECURSIVE Sum(_, _)
Sum(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(S \ {x}, f)

\* Helper to check if a coordinate is on the board.
IsOnBoard(i, j) == i \in 1..N /\ j \in 1..N

\* Returns the state of a cell at (i, j) in a given grid g.
\* Cells outside the board are considered dead (FALSE).
CellState(g, i, j) ==
  IF IsOnBoard(i, j) THEN g[<<i, j>>] ELSE FALSE

\* Returns the set of 8 neighbor coordinates for a cell at (i, j).
Neighbors(i, j) ==
  { <<i-1, j-1>>, <<i-1, j>>, <<i-1, j+1>>,
    <<i,   j-1>>,             <<i,   j+1>>,
    <<i+1, j-1>>, <<i+1, j>>, <<i+1, j+1>> }

\* Counts the number of live neighbors for a cell at (i, j) in a given grid g.
LiveNeighbors(g, i, j) ==
  LET IsAlive(pos) == IF CellState(g, pos[1], pos[2]) THEN 1 ELSE 0
  IN Sum(Neighbors(i, j), IsAlive)

\* The initial state is any valid grid configuration.
Init ==
  grid \in [BoardCoords -> BOOLEAN]

\* The next-state relation, which computes the next grid state based on
\* the standard rules of Conway's Game of Life.
Next ==
  LET
    \* Determines the next state of a single cell based on its current state
    \* and the number of its live neighbors.
    NextCellState(pos) ==
      LET currentIsAlive == grid[pos]
          neighborCount  == LiveNeighbors(grid, pos[1], pos[2])
      IN
        \* A live cell survives if it has 2 or 3 neighbors.
        IF currentIsAlive THEN
          neighborCount \in {2, 3}
        \* A dead cell becomes alive if it has exactly 3 neighbors.
        ELSE
          neighborCount = 3
  IN
    \* The next grid is a new function where each cell's value is updated.
    grid' = [pos \in BoardCoords |-> NextCellState(pos)]

\* The temporal specification for the system.
Spec == Init /\ [][Next]_vars

=============================================================================