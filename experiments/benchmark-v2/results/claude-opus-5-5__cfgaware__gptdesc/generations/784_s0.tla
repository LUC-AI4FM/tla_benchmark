---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLE grid

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}

TypeOK == grid \in [Pos -> BOOLEAN]

sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
    IF x = 0 \/ y = 0 \/ x > N \/ y > N
    THEN 0
    ELSE IF grid[<<x, y>>] THEN 1 ELSE 0

score(p) ==
    LET nbrs   == {d \in {-1, 0, 1} \X {-1, 0, 1} : d /= <<0, 0>>}
        points == {<<p[1] + d[1], p[2] + d[2]>> : d \in nbrs}
    IN  Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |->
                IF \/ (grid[p] /\ score(p) \in {2, 3})
                   \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================