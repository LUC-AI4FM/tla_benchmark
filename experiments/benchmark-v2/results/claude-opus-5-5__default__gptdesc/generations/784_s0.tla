---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == <<grid>>

(* The set of board coordinates *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Sum the values of function f over the finite set S *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

(* Cell values extended with a border of dead cells outside the board *)
sc == [p \in (0..(N + 1)) \X (0..(N + 1)) |->
          IF p \in Pos /\ grid[p] THEN 1 ELSE 0]

(* The eight neighbor positions of a cell *)
Neighbors(p) ==
    {<<p[1] + dx, p[2] + dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1}}
        \ {p}

(* Number of live neighbors of a cell *)
Score(p) == Sum(sc, Neighbors(p))

TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |->
                IF grid[p]
                    THEN Score(p) \in {2, 3}
                    ELSE Score(p) = 3]

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
=============================================================================