------------------------------- MODULE ConwayGameOfLife -------------------------------

EXTENDS FiniteSets, TLC

CONSTANTS N

VARIABLE grid

Sum(S) == \E f \in [S -> BOOLEAN] : \A x \in S : f[x] = grid[x] : \Sum_{x \in S} (IF f[x] THEN 1 ELSE 0)

Neighbors(x, y) == 
    LET around == {(x-1, y-1), (x-1, y), (x-1, y+1),
                  (x, y-1),           (x, y+1),
                  (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN  {p \in around : \/ p = <<x, y>>
                         \/ /\ p[1] >= 1
                            /\ p[1] <= N
                            /\ p[2] >= 1
                            /\ p[2] <= N}

LiveNeighbors(x, y) == Sum(Neighbors(x, y))

NextGrid ==
    [p \in {<<x, y>> : x \in 1..N /\ y \in 1..N} |-> 
        LET liveCount == LiveNeighbors(p[1], p[2])
        IN  CASE grid[p] = TRUE /\ liveCount \notin {2, 3} -> FALSE
            [] grid[p] = FALSE /\ liveCount = 3 -> TRUE
            [] OTHER -> grid[p]]

Init ==
    /\ grid \in [<<1..N>> X <<1..N>> -> BOOLEAN]
    /\ \A x \in 1..N, y \in 1..N : \/ grid[<<x, y>>] = TRUE 
                                          \/ grid[<<x, y>>] = FALSE

Next ==
    grid' = NextGrid

Spec == 
    Init /\ [][Next]_<<grid>>

=============================================================================