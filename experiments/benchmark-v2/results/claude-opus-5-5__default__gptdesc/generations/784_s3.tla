---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == <<grid>>

Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

ExtPos == (0..(N + 1)) \X (0..(N + 1))

RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

sc[p \in ExtPos] ==
    IF p \in Pos
    THEN IF grid[p] THEN 1 ELSE 0
    ELSE 0

Neighbors(p) ==
    {<<p[1] + dx, p[2] + dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1}} \ {p}

score(p) == Sum(sc, Neighbors(p))

TypeOK == grid \in [Pos -> BOOLEAN]

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |->
                IF \/ (grid[p] /\ score(p) \in {2, 3})
                   \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
====