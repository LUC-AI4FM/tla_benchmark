---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

Board == (1..N) \X (1..N)

Offsets == { <<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : ~(dx = 0 /\ dy = 0) }

Add(p, o) == << p[1] + o[1], p[2] + o[2] >>

Neighbors(p) == { Add(p, o) : o \in Offsets }

RECURSIVE Sum(_)
Sum(S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN x + Sum(S \ {x})

RECURSIVE SumBy(_, _)
SumBy(A, f(_)) ==
  IF A = {} THEN 0
  ELSE
    LET x == CHOOSE y \in A : TRUE
    IN f(x) + SumBy(A \ {x}, f)

LiveNeighborCount(p) ==
  LET L(q) == IF q \in Board /\ grid[q] THEN 1 ELSE 0
  IN SumBy(Neighbors(p), L)

TypeOK == grid \in [Board -> BOOLEAN]

CountOK == \A p \in Board : LiveNeighborCount(p) \in 0..8

Inv == TypeOK /\ CountOK

Init == TypeOK

Next ==
  grid' = [ p \in Board |->
              LET n == LiveNeighborCount(p)
              IN IF grid[p] THEN (n = 2) \/ (n = 3) ELSE n = 3
          ]

Spec == Init /\ [][Next]_<<grid>>
====