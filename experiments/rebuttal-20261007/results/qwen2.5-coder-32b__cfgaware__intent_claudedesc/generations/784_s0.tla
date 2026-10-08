------------------------------- MODULE GameOfLife -------------------------------

CONSTANTS N \* Size of the grid (N x N)

VARIABLES grid \* The current state of the grid

\* Define a set of all valid positions in the grid
GridPositions == { <<x, y>> \in [1..N] \X [1..N] }

\* Define a function to check if a position is within the grid boundaries
InBounds(p) == p \in GridPositions

\* Define a function to get the state of a cell at a given position
GetCellState(g, p) == IF InBounds(p) THEN g[p] ELSE FALSE

\* Define a set of all 8 possible neighbor positions relative to a given cell
Neighbors(p) == { <<p[1]+dx, p[2]+dy>> \in GridPositions : dx \in {-1..1} /\ dy \in {-1..1} /\ <<dx, dy>> /= <<0, 0>> }

\* Define a function to count the number of live neighbors for a given cell
CountLiveNeighbors(g, p) == Cardinality({ n \in Neighbors(p) : GetCellState(g, n) })

\* Define the rule for updating a single cell based on its current state and live neighbor count
UpdateCell(g, p) ==
  LET liveNeighbors == CountLiveNeighbors(g, p)
      currentState == GetCellState(g, p)
  IN CASE currentState /\ (liveNeighbors = 2 \/ liveNeighbors = 3) -> TRUE
     [] \lnot currentState /\ liveNeighbors = 3 -> TRUE
     [] OTHER -> FALSE

\* Define the rule for updating the entire grid to the next state
NextGrid(g) == [ p \in GridPositions |-> UpdateCell(g, p) ]

\* Define a predicate that checks if a given grid is valid (i.e., all positions are mapped to TRUE or FALSE)
IsValidGrid(g) == g \in [GridPositions -> BOOLEAN]

\* Define the initial condition for the specification
Init == /\ IsValidGrid(grid)

\* Define the next-state relation for the specification
Next == LET newGrid == NextGrid(grid)
        IN /\ IsValidGrid(newGrid)
           /\ grid' = newGrid

\* Define the type invariants that must hold throughout the execution
TypeOK == Init /\ []IsValidGrid(grid)

\* Define the complete specification
Spec == Init /\ [][Next]_<<grid>>

===============================================================================