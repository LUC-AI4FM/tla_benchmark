MODULE GameOfLife

EXTENDS Integers

CONSTANT N

VARIABLE grid

Board == {1..N} \times {1..N}

Neighbors(p) ==
  { q \in Board :
      Abs(q[1] - p[1]) <= 1
      /\ Abs(q[2] - p[2]) <= 1
      /\ q /= p }

CountLiveNeighbors(g, p) ==
  \sum q \in Neighbors(p) : IF g[q] THEN 1 ELSE 0

LifeRule(g, p) ==
  IF g[p] THEN
    (CountLiveNeighbors(g,p) = 2 \/ CountLiveNeighbors(g,p) = 3)
  ELSE
    (CountLiveNeighbors(g,p) = 3)

Init == grid \in [Board -> BOOLEAN]

Next ==
  \/ grid' = [p \in Board |-> LifeRule(grid, p)]
  \/ UNCHANGED <<grid>>

Spec == Init /\ [] [][Next]_grid

TypeInvariant == grid \in [Board -> BOOLEAN]