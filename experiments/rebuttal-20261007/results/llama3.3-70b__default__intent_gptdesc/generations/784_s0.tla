```tla
MODULE GameOfLife

EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES grid, steps

Init ==
  /\ grid \in [1..N -> {True, False}]
  /\ steps = 0

Next ==
  /\ steps' = steps + 1
  /\ grid' = [i \in 1..N, j \in 1..N |-> 
              IF grid[i, j] THEN
                (NeighborCount(i, j) = 2) OR (NeighborCount(i, j) = 3)
              ELSE
                NeighborCount(i, j) = 3]

NeighborCount(i, j) ==
  LET neighbors == {
    <<(i + 1) % N + 1, j>,
    <<(i - 1) % N + 1, j>,
    <i, (j + 1) % N + 1>,
    <i, (j - 1) % N + 1>,
    <<(i + 1) % N + 1, (j + 1) % N + 1>,
    <<(i + 1) % N + 1, (j - 1) % N + 1>,
    <<(i - 1) % N + 1, (j + 1) % N + 1>,
    <<(i - 1) % N + 1, (j - 1) % N + 1>
  }
  IN
    Cardinality({n \in neighbors: grid[n[1], n[2]]})

TypeCorrectness ==
  grid \in [1..N -> {True, False}]

UpdateDeterminism ==
  /\ TypeCorrectness
  /\ \A i, j \in 1..N:
      IF grid[i, j] THEN
        (NeighborCount(i, j) = 2) OR (NeighborCount(i, j) = 3)
      ELSE
        NeighborCount(i, j) = 3

Invariance ==
  TypeCorrectness

StillLife ==
  /\ \E s \in [1..N -> {True, False}]:
    /\ grid = s
    /\ grid' = s

Oscillator ==
  /\ \E s \in [1..N -> {True, False}], p \in Nat:
    /\ grid = s
    /\ grid'[p] = s

Glider ==
  /\ \E s \in [1..N -> {True, False}], v \in (1..N -> Int), p \in Nat:
    /\ grid = s
    /\ grid'[p] = [i, j |-> IF <i - v[i], j - v[j]> \in Domain(s) THEN s[<i - v[i], j - v[j]>] ELSE False]

Progress ==
  <>[\A s \in [1..N -> {True, False}]: 
    /\ grid = s
    /\ \E p \in Nat: grid'[p] = s]

Spec ==
  /\ Init
  /\ [][Next]_grid
  /\ WF_vars(Next)

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []UpdateDeterminism
THEOREM Spec => []Invariance
THEOREM Spec => StillLife
THEOREM Spec => Oscillator
THEOREM Spec => Glider
THEOREM Spec => Progress

```
Note: The above TLA+ specification models Conway's Game of Life on a finite N×N toroidal board. It includes the initial state, next-state relation, type correctness, update determinism, invariance, still life, oscillator, glider, and progress properties. However, please note that this is a simplified version and might need further refinement based on specific requirements or constraints not mentioned in the problem description.