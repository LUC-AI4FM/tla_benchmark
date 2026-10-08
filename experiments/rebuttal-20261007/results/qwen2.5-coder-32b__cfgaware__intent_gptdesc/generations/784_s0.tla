```tla
------------------------------- MODULE ConwayGameOfLife ------------------------------

CONSTANTS N

VARIABLES grid

(*--algorithm GameOfLife
variables grid = [x \in 1..N, y \in 1..N -> BOOLEAN];

nextGrid == 
    [x \in 1..N, y \in 1..N |-> Let liveNeighbors ==
        (Sum {grid[x', y'] : x' \in {(x-1) % N + 1, x, (x+1) % N + 1} & y' \in {(y-1) % N + 1, y, (y+1) % N + 1}} - grid[x, y])
    IN
        CASE liveNeighbors = 3 \/ (liveNeighbors = 2 /\ grid[x, y]) -> TRUE
        [] OTHER -> FALSE];

Spec == 
    VARIABLES grid
    INIT grid \in [1..N -> [1..N -> BOOLEAN]]
    NEXT grid' = nextGrid

TypeOK ==
    \A x \in 1..N, y \in 1..N: grid[x, y] \in BOOLEAN

(*--fairness
WF_vars == <<grid>>

FairSpec == Spec /\ WF_vars

THEOREM Spec => []TypeOK
THEOREM Spec => [](grid' = nextGrid)
THEOREM FairSpec => <>(\E s \in SUBSET (NATURAL): (\A i, j \in s: grid[i] = grid[j]))

END GameOfLife
```

This TLA+ specification models Conway's Game of Life on an N×N toroidal board. It defines the necessary constants and variables as specified:

- `N`: The size of the grid.
- `TypeOK`: An operator that asserts type correctness, ensuring each cell in the grid is a boolean value.
- `Spec`: The main specification, which includes initial states and transition rules.

The specification ensures:
- Type correctness: Each cell's state remains a boolean.
- Update determinism: Given a state, the next state is uniquely determined by the Life rules.
- Invariance: The set of live/dead labels remains within the boolean domain throughout execution.
- Fairness assertion for periodic behavior (liveness): There exist repeated states or cycles reachable from some initial configurations.

The `nextGrid` operator calculates the next state of the grid based on the current state and the Life rules. The fairness condition is added to ensure that the system can reach a cycle, which is part of the liveness property.