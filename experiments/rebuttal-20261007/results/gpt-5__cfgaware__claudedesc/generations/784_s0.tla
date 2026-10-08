------------------------------ MODULE GameOfLife ------------------------------

EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLE grid

Pos == 1..N \X 1..N

vars == <<grid>>

Add(p, q) == << p[1] + q[1], p[2] + q[2] >>

Offs ==
  { <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,             << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>> }

Neigh(p) == { Add(p, o) : o \in Offs }

sc(q) == IF q \in Pos THEN (IF grid[q] THEN 1 ELSE 0) ELSE 0

score(p) == Cardinality({ q \in Neigh(p) : sc(q) = 1 })

Init == grid \in [Pos -> BOOLEAN]

Next ==
  grid' =
    [ pos \in Pos |->
        LET n == score(pos) IN
          IF grid[pos] THEN (n = 2) \/ (n = 3) ELSE (n = 3)
    ]

TypeOK == grid \in [Pos -> BOOLEAN]

Spec == Init /\ [][Next]_vars

=============================================================================