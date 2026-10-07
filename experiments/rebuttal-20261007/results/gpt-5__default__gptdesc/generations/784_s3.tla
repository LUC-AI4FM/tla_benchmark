------------------------------ MODULE GameOfLife ------------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES grid

Board == (1..N) \X (1..N)

Offsets ==
  { <<-1,-1>>, <<-1,0>>, <<-1,1>>,
    << 0,-1>>,            << 0,1>>,
    << 1,-1>>, << 1,0>>,  << 1,1>> }

AddPos(p, d) == << p[1] + d[1], p[2] + d[2] >>

AliveAt(p) == IF p \in Board THEN grid[p] ELSE FALSE

RECURSIVE Sum(_,_)
Sum(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE e \in S: TRUE IN
      f[x] + Sum(S \ {x}, f)

LiveNeighborCount(p) ==
  LET f == [ d \in Offsets |-> IF AliveAt(AddPos(p, d)) THEN 1 ELSE 0 ]
  IN Sum(Offsets, f)

NextCellValue(p) ==
  LET n == LiveNeighborCount(p) IN
    IF grid[p] THEN (n = 2) \/ (n = 3) ELSE n = 3

Init == grid \in [Board -> BOOLEAN]

Next == grid' = [ p \in Board |-> NextCellValue(p) ]

Spec == Init /\ [][Next]_grid

TypeInv == grid \in [Board -> BOOLEAN]

OutsideDeadInv == \A p: ~(p \in Board) => ~AliveAt(p)

NeighborCountRangeInv == \A p \in Board: LiveNeighborCount(p) \in 0..8

=============================================================================