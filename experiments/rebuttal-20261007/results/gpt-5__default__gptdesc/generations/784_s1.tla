------------------------------ MODULE GameOfLife ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  Board coordinates are pairs <<i, j>> with i, j in 1..N.
*)
Board == (1..N) \X (1..N)

VARIABLES grid

vars == << grid >>

(*
  Offsets for the 8 neighboring cells.
*)
Offsets == ((-1..1) \X (-1..1)) \ { <<0, 0>> }

(*
  Add an offset to a position.
*)
AddPos(p, o) == << p[1] + o[1], p[2] + o[2] >>

(*
  Set of neighbor positions for a given cell (may include positions outside Board).
*)
Neighbors(p) == { AddPos(p, o) : o \in Offsets }

(*
  Cells outside the Board are treated as dead.
*)
IsAliveAt(q) == IF q \in Board THEN grid[q] ELSE FALSE

BoolToInt(b) == IF b THEN 1 ELSE 0

RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE
            LET x == CHOOSE x \in S: TRUE IN
              x + Sum(S \ {x})

(*
  Number of live neighbors for position p.
*)
CountLiveNeighbors(p) ==
  Sum({ BoolToInt(IsAliveAt(q)) : q \in Neighbors(p) })

(*
  Initial states: any boolean labeling of the board.
*)
Init == grid \in [Board -> BOOLEAN]

(*
  Next-state relation: standard Conway's Game of Life rule.
*)
Next ==
  grid' = [ p \in Board |->
              LET n == CountLiveNeighbors(p) IN
                IF grid[p]
                  THEN (n = 2) \/ (n = 3)
                  ELSE (n = 3)
          ]

(*
  Safety invariants (type and bounds).
*)
TypeInv == grid \in [Board -> BOOLEAN]
LiveNeighborCountBounds == \A p \in Board: CountLiveNeighbors(p) \in 0..8
Inv == TypeInv /\ LiveNeighborCountBounds

(*
  Temporal specification: arbitrary initialization followed by repeated Next,
  with stuttering allowed.
*)
Spec == Init /\ [][Next]_vars

=============================================================================