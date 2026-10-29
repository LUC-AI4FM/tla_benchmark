---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == <<grid>>

-----------------------------------------------------------------------------
(* Grid geometry *)

Coord == 1..N

Pos == Coord \X Coord

Grids == [Pos -> BOOLEAN]

AbsDiff(a, b) == IF a >= b THEN a - b ELSE b - a

(* In-bounds neighbors of a position. Out-of-bounds positions are never  *)
(* included, so they count as permanently dead.                          *)
Neighbors(p) ==
    { q \in Pos :
        /\ q /= p
        /\ AbsDiff(q[1], p[1]) <= 1
        /\ AbsDiff(q[2], p[2]) <= 1 }

LiveNeighborCount(g, p) == Cardinality({ q \in Neighbors(p) : g[q] })

(* Standard Game of Life rule (B3/S23) *)
NextCellState(g, p) ==
    LET n == LiveNeighborCount(g, p) IN
    IF g[p]
        THEN n \in {2, 3}
        ELSE n = 3

(* The successor of a grid is a function of that grid alone *)
NextGrid(g) == [p \in Pos |-> NextCellState(g, p)]

-----------------------------------------------------------------------------
(* Specification *)

(* Any arbitrary initial configuration *)
Init == grid \in Grids

(* Simultaneous update of the entire grid *)
Step == grid' = NextGrid(grid)

Next == Step

Spec == Init /\ [][Next]_vars

(* Variant that requires generations to keep being computed *)
FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

(* The grid is always a valid mapping from positions to alive/dead *)
TypeOK == grid \in Grids

(* Determinism: every non-stuttering step produces exactly the unique    *)
(* successor configuration NextGrid(grid).                               *)
Deterministic == [][grid' = NextGrid(grid)]_vars

(* Determinism as a static fact: for every configuration there is        *)
(* exactly one successor configuration permitted by the rule.            *)
UniqueSuccessor ==
    \A g \in Grids :
        /\ NextGrid(g) \in Grids
        /\ \A h1, h2 \in Grids :
              (/\ h1 = NextGrid(g)
               /\ h2 = NextGrid(g)) => h1 = h2

(* The rule is well defined: neighbor counts are within 0..8 *)
NeighborCountBounded ==
    \A p \in Pos : LiveNeighborCount(grid, p) \in 0..8

THEOREM Spec => []TypeOK
THEOREM Spec => Deterministic
=============================================================================