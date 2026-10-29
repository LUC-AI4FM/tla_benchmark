------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLE grid

vars == <<grid>>

(***************************************************************************)
(* Board coordinates                                                        *)
(***************************************************************************)
Pos == {<<x, y>> : x, y \in 1..N}

(***************************************************************************)
(* Extended coordinates: the board plus a one-cell border of dead cells.    *)
(***************************************************************************)
ExtPos == (0..(N + 1)) \X (0..(N + 1))

(***************************************************************************)
(* Sum of the values of function f over a finite set S                      *)
(***************************************************************************)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

(***************************************************************************)
(* Score of a cell: 1 if alive and on the board, 0 otherwise.               *)
(* Cells outside the board are treated as dead.                             *)
(***************************************************************************)
sc == [p \in ExtPos |->
         IF p \in Pos
         THEN IF grid[p] THEN 1 ELSE 0
         ELSE 0]

(***************************************************************************)
(* The eight neighbors of a board position                                  *)
(***************************************************************************)
Nbhd(v) ==
    {<<v[1] + dx, v[2] + dy>> : dx, dy \in {-1, 0, 1}} \ {v}

(***************************************************************************)
(* Number of live neighbors of a board position                             *)
(***************************************************************************)
LiveNeighbors(v) == Sum(sc, Nbhd(v))

(***************************************************************************)
(* Standard Life rule                                                       *)
(***************************************************************************)
Rule(alive, n) ==
    \/ alive /\ n \in {2, 3}
    \/ ~alive /\ n = 3

TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |-> Rule(grid[p], LiveNeighbors(p))]

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
===============================================================================