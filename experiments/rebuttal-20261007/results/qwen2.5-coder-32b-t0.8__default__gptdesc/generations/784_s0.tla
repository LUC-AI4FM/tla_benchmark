------------------------------- MODULE ConwayLife -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat \ {0}

VARIABLES grid

(*--algorithm life
variables grid = [x \in 1..N, y \in 1..N -> FALSE]
begin Init;
    while TRUE do Next; od;
end algorithm*)

Sum(S) == \E s: \A x \in S: s[x] = (\A y \in S: IF y = x THEN s[y] ELSE FALSE)
Boundary(x, y) == (x > 0 /\ x <= N /\ y > 0 /\ y <= N)
LiveNeighbors(grid, x, y) ==
    LET neighbors == {(x-1, y-1), (x-1, y), (x-1, y+1),
                     (x, y-1),         (x, y+1),
                     (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN  \Sum{grid[x', y'] : <<x', y'>> \in neighbors /\ Boundary(x', y')}
    
Init == grid \in [1..N -> [1..N -> BOOLEAN]]

Next ==
    \E newGrid: 
        /\ newGrid \in [1..N -> [1..N -> BOOLEAN]]
        /\ \A x \in 1..N, y \in 1..N:
            LET liveCount == LiveNeighbors(grid, x, y)
            IN  (liveCount = 3 \/ (grid[x, y] /\ liveCount = 2))
                <-> newGrid[x, y]
        /\ grid' = newGrid

Spec ==
    Init /\ [][Next]_<<grid>>

================================================================================