MODULE Life
EXTENDS Naturals

CONSTANT N \in Nat

BoardCoords == { [x |-> i, y |-> j] : i \in 1..N /\ j \in 1..N }

Neighbors(p) ==
    { q \in BoardCoords :
        q.x \in p.x-1 .. p.x+1 /\ q.y \in p.y-1 .. p.y+1
          & q \not= p }

Life(g) ==
    [p \in BoardCoords |-> 
        LET n == SUM q \in Neighbors(p) : IF g[q] THEN 1 ELSE 0 IN
            IF (g[p] /\ (n = 2 \/ n = 3)) \/ (~g[p] /\ n = 3)
                THEN TRUE
                ELSE FALSE ]

VARIABLES grid

Init ==
    grid = [p \in BoardCoords |-> FALSE]

Next ==
    \E newGrid \in [BoardCoords -> BOOLEAN] :
        (newGrid = Life(grid) \/ newGrid = grid) 
        /\ grid' = newGrid

Spec ==
    Init /\ [][Next]_<<grid>>

END MODULE