----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES grid

Board == (1..N) \X (1..N)

(*
  Safety invariants
*)
TypeInv == grid \in [Board -> BOOLEAN]
NeighborCountBound == \A p \in Board: CountLiveNeighbors(p) \in 0..8

(*
  Helper operators
*)
NeighborOffsets ==
  {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
   << 0, -1>>,             << 0, 1>>,
   << 1, -1>>, << 1, 0>>, << 1, 1>>}

Add(p, d) == << p[1] + d[1], p[2] + d[2] >>

Neighbors(p) == { Add(p, d) : d \in NeighborOffsets }

IsAliveAt(p) == IF p \in Board THEN grid[p] ELSE FALSE

RECURSIVE SumOver(_, _)
SumOver(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN f[x] + SumOver(S \ {x}, f)

CountLiveNeighbors(p) ==
  SumOver(Neighbors(p), LAMBDA n: IF IsAliveAt(n) THEN 1 ELSE 0)

(*
  Init and Next
*)
Init == grid \in [Board -> BOOLEAN]

Next ==
  grid' =
    [p \in Board |->
       LET c == CountLiveNeighbors(p)
       IN (c = 3) \/ (grid[p] /\ c = 2)
    ]

Spec == Init /\ [][Next]_grid
=============================================================================