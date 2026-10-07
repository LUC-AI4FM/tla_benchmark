---- MODULE GameOfLife ----
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES grid

(*
  Basic sets and board geometry
*)
Bool == {TRUE, FALSE}
Board == 1..N \X 1..N

(*
  Neighbor offsets (8-neighborhood)
*)
Offsets ==
  {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,             << 0, 1>>,
    << 1, -1>>, << 1, 0>>,  << 1, 1>>
  }

(*
  Tuple addition for board coordinates
*)
AddTuples(p, q) == << p[1] + q[1], p[2] + q[2] >>

Neighbors(p) == { AddTuples(p, d) : d \in Offsets }

(*
  Boundary handling: cells outside the board are dead
*)
AliveAt(pos) == IF pos \in Board THEN grid[pos] ELSE FALSE

(*
  Sum over a finite set of integers
*)
RECURSIVE Sum(_)
Sum(S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN x + Sum(S \ {x})

(*
  Count of live neighbors for a position p
*)
LiveNeighborCount(p) ==
  Sum({ IF AliveAt(nbr) THEN 1 ELSE 0 : nbr \in Neighbors(p) })

(*
  Conway's Life rule for a single position p
*)
LifeRule(p) ==
  LET c == LiveNeighborCount(p) IN
    IF grid[p] THEN (c \in {2, 3}) ELSE (c = 3)

(*
  Typing invariant
*)
TypeInvariant == grid \in [Board -> Bool]

(*
  Neighbor-count bounds (always 0..8)
*)
NeighborCountBounds == \A p \in Board : LiveNeighborCount(p) \in 0..8

Init == TypeInvariant

Next ==
  /\ grid' = [ p \in Board |-> LET c == LiveNeighborCount(p) IN IF grid[p] THEN (c = 2) \/ (c = 3) ELSE (c = 3) ]

Spec == Init /\ [][Next]_grid

====