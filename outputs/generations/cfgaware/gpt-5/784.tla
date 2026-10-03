----------------------------- MODULE Life -----------------------------
EXTENDS Naturals, Integers

CONSTANT N
VARIABLE grid

Board == (1..N) \X (1..N)

Deltas ==
  { <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,            << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>> }

Add(p, q) == << p[1] + q[1], p[2] + q[2] >>

InBounds(p) == p \in Board

BoolToInt(b) == IF b THEN 1 ELSE 0

AliveAt(p) == IF InBounds(p) THEN grid[p] ELSE FALSE

Nbrs(p) == { Add(p, d) : d \in Deltas }

RECURSIVE Sum(_)
Sum(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN x + Sum(S \ {x})

LiveNeighbors(p) == Sum({ BoolToInt(AliveAt(q)) : q \in Nbrs(p) })

UpdateCell(p) ==
  LET a == AliveAt(p) IN
  LET n == LiveNeighbors(p) IN
    (a /\ (n = 2 \/ n = 3)) \/ (~a /\ n = 3)

TypeOK ==
  /\ N \in Nat \ {0}
  /\ grid \in [Board -> BOOLEAN]

Init == grid \in [Board -> BOOLEAN]

Next == grid' = [p \in Board |-> UpdateCell(p)]

Spec == Init /\ [][Next]_grid
=======================================================================