---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

VARIABLES grid

\* Define the set of all valid positions on the grid
Positions == (0..N-1) \X (0..N-1)

\* Define the possible states for each cell
CellState == {0, 1}  \* 0 = dead, 1 = alive

\* Type invariant: grid is a valid mapping from positions to cell states
TypeInvariant == grid \in [Positions -> CellState]

\* Get the state of a cell, treating out-of-bounds as dead
GetCell(g, x, y) == 
    IF x >= 0 /\ x < N /\ y >= 0 /\ y < N 
    THEN g[<<x, y>>]
    ELSE 0

\* Define the 8 neighbor offsets
NeighborOffsets == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
                    <<0, -1>>,            <<0, 1>>,
                    <<1, -1>>,  <<1, 0>>,  <<1, 1>>}

\* Count the number of live neighbors for a cell at position (x, y)
CountLiveNeighbors(g, x, y) ==
    LET neighbors == {GetCell(g, x + offset[1], y + offset[2]) : offset \in NeighborOffsets}
    IN Cardinality({offset \in NeighborOffsets : GetCell(g, x + offset[1], y + offset[2]) = 1})

\* Compute the next state of a cell based on Game of Life rules
NextCellState(g, x, y) ==
    LET currentState == g[<<x, y>>]
        liveNeighbors == CountLiveNeighbors(g, x, y)
    IN IF currentState = 1
       THEN \* Live cell: survives with 2 or 3 neighbors
            IF liveNeighbors = 2 \/ liveNeighbors = 3
            THEN 1
            ELSE 0
       ELSE \* Dead cell: becomes alive with exactly 3 neighbors
            IF liveNeighbors = 3
            THEN 1
            ELSE 0

\* Compute the next grid state by applying rules to all cells simultaneously
NextGrid(g) == [pos \in Positions |-> NextCellState(g, pos[1], pos[2])]

\* Initial state: any valid grid configuration
Init == grid \in [Positions -> CellState]

\* Next state: evolve the entire grid according to Game of Life rules
Next == grid' = NextGrid(grid)

\* The specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_grid /\ WF_grid(Next)

\* Safety Invariant: The grid state is always valid
SafetyInvariant == TypeInvariant

\* Property: Evolution is deterministic (expressed as: from any state, 
\* there is exactly one possible next state)
\* This is inherently satisfied by the functional definition of NextGrid
DeterministicEvolution == 
    [][grid' = NextGrid(grid)]_grid

\* Property: All cell values are valid (either 0 or 1)
ValidCellStates == \A pos \in Positions : grid[pos] \in {0, 1}

\* Property: The grid covers exactly the expected positions
ValidGridDomain == DOMAIN grid = Positions

=============================================================================