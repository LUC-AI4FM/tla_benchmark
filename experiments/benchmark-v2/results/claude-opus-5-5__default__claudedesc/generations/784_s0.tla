---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat

VARIABLE grid

vars == <<grid>>

RECURSIVE Sum(_, _)
Sum(f, D) == IF D = {} THEN 0
             ELSE LET x == CHOOSE x \in D : TRUE
                  IN f[x] + Sum(f, D \ {x})

Pos == {<<x, y>> : x, y \in 1..N}

TypeOK == grid \in [Pos -> BOOLEAN]

sc(<<x, y>>) == CASE \/ x \notin 1..N
                     \/ y \notin 1..N -> 0
                  [] grid[<<x, y>>] -> 1
                  [] OTHER -> 0

score(p) == LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
                points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
            IN Sum([q \in points |-> sc(q)], points)

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |->
                    IF \/  (grid[p] /\ score(p) \in {2, 3})
                       \/ (~grid[p] /\ score(p) = 3)
                    THEN TRUE
                    ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================