---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == grid

(***************************************************************************)
(* Board coordinates                                                       *)
(***************************************************************************)
Pos == {<<x, y>> : x, y \in 1..N}

(***************************************************************************)
(* Sum of f[x] over all x in the finite set S                              *)
(***************************************************************************)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE x \in S : TRUE
                  IN  f[x] + Sum(f, S \ {x})

(***************************************************************************)
(* Score of a cell on the extended board: cells outside the board          *)
(* (the border ring) are treated as dead.                                  *)
(***************************************************************************)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
    IF x = 0 \/ y = 0 \/ x = N + 1 \/ y = N + 1
       THEN 0
       ELSE IF grid[<<x, y>>] THEN 1 ELSE 0

(***************************************************************************)
(* Number of live neighbours of position p                                 *)
(***************************************************************************)
score(p) ==
    LET nbrs   == {d \in {-1, 0, 1} \X {-1, 0, 1} : d /= <<0, 0>>}
        points == {<<p[1] + d[1], p[2] + d[2]>> : d \in nbrs}
    IN  Sum(sc, points)

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK == grid \in [Pos -> BOOLEAN]

(***************************************************************************)
(* Initial condition: any configuration of live and dead cells             *)
(***************************************************************************)
Init == grid \in [Pos -> BOOLEAN]

(***************************************************************************)
(* Standard Life rule: a live cell survives with 2 or 3 live neighbours,   *)
(* a dead cell becomes alive with exactly 3 live neighbours.               *)
(***************************************************************************)
Next ==
    grid' = [p \in Pos |->
                IF \/ (grid[p] /\ score(p) \in {2, 3})
                   \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

=============================================================================