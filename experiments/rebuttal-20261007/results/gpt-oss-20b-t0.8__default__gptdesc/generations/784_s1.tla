------------------------------ MODULE Life ------------------------------
EXTENDS Integers

CONSTANT N \in Nat
-- board indices are 1 .. N

VARIABLES grid

Board == { <<i, j>> : i \in 1..N /\ j \in 1..N }

Init ==
    /\ grid \in [Board -> BOOLEAN]

BoolToInt(b) == IF b THEN 1 ELSE 0

Neighbors(p) ==
    { q \in Board :
        (Abs(q[1]-p[1]) <= 1 /\ Abs(q[2]-p[2]) <= 1)
         /\ q != p }

CountLiveNeighbors(g, p) ==
    \sum q \in Neighbors(p) : BoolToInt(g[q])

LifeRule(g, p) ==
    LET n == CountLiveNeighbors(g,p) IN
        (g[p] /\ (n = 2 \/ n = 3)) \/ (~g[p] /\ (n = 3))

Next ==
    \E newGrid \in [Board -> BOOLEAN] :
        (\A p \in Board : newGrid[p] = LifeRule(grid, p))

Step == Next \/ UNCHANGED grid

vars == {grid}

Spec == Init /\ [][Step]_vars
=============================================================================