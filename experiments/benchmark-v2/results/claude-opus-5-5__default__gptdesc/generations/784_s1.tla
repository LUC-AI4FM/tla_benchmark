------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == <<grid>>

-----------------------------------------------------------------------------
(* Board coordinates *)

Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Offsets of the eight neighbouring cells *)
Offsets == ({-1, 0, 1} \X {-1, 0, 1}) \ {<<0, 0>>}

(* Sum of the values of function f over the finite set S *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {}
    THEN 0
    ELSE LET e == CHOOSE e \in S : TRUE
         IN  f[e] + Sum(f, S \ {e})

(* Value of a cell: 1 if alive, 0 if dead. Cells outside the board are dead. *)
sc(x, y) ==
    IF <<x, y>> \in Pos
    THEN IF grid[<<x, y>>] THEN 1 ELSE 0
    ELSE 0

(* Number of live neighbours of the cell at (x, y) *)
LiveNeighbours(x, y) ==
    Sum([d \in Offsets |-> sc(x + d[1], y + d[2])], Offsets)

(* Standard Life rule *)
NextCellState(p) ==
    LET x == p[1]
        y == p[2]
        n == LiveNeighbours(x, y)
    IN  \/ (grid[p] /\ n \in {2, 3})
        \/ (~grid[p] /\ n = 3)

-----------------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |-> NextCellState(p)]

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================