----------------------------- MODULE GameOfLife -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES grid

Cells == 1..N
Pos == Cells \X Cells

TypeOK == grid \in [Pos -> BOOLEAN]

InBounds(i, j) == (i \in Cells) /\ (j \in Cells)

sc(g, i, j) ==
  IF InBounds(i, j) THEN
    IF g[<<i, j>>] THEN 1 ELSE 0
  ELSE 0

score(g, i, j) ==
  sc(g, i-1, j-1) +
  sc(g, i-1, j  ) +
  sc(g, i-1, j+1) +
  sc(g, i,   j-1) +
  sc(g, i,   j+1) +
  sc(g, i+1, j-1) +
  sc(g, i+1, j  ) +
  sc(g, i+1, j+1)

Init == TypeOK

Next ==
  grid' =
    [ p \in Pos |->
        LET i == p[1] IN
        LET j == p[2] IN
        LET n == score(grid, i, j) IN
          IF grid[p] THEN (n = 2) \/ (n = 3) ELSE n = 3
    ]

vars == << grid >>

Spec == Init /\ [][Next]_vars

============================================================================