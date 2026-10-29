---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLE grid

vars == <<grid>>

Pos == (1..N) \X (1..N)

IsNeighbor(p, q) ==
    /\ q /= p
    /\ p[1] - 1 <= q[1] /\ q[1] <= p[1] + 1
    /\ p[2] - 1 <= q[2] /\ q[2] <= p[2] + 1

Neighbors(p) == { q \in Pos : IsNeighbor(p, q) }

LiveNeighborCount(g, p) == Cardinality({ q \in Neighbors(p) : g[q] })

NextCellState(g, p) ==
    LET n == LiveNeighborCount(g, p) IN
    IF g[p]
        THEN n = 2 \/ n = 3
        ELSE n = 3

NextGrid(g) == [p \in Pos |-> NextCellState(g, p)]

TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = NextGrid(grid)

Spec == Init /\ [][Next]_vars

Deterministic ==
    \A g \in [Pos -> BOOLEAN] :
        \A h1, h2 \in [Pos -> BOOLEAN] :
            (h1 = NextGrid(g) /\ h2 = NextGrid(g)) => h1 = h2

====