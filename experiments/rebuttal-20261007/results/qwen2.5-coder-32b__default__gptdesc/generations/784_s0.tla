------------------------------- MODULE ConwayGameOfLife -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES grid

(*--algorithm ConwayGameOfLife
variables grid = [x \in 1..N, y \in 1..N |-> FALSE];
begin
while TRUE do
    with newGrid <- [x \in 1..N, y \in 1..N |-> NextState(x, y)];
    grid := newGrid;
end while;
end algorithm*)

Sum(S) == \E s \in SUBSET S : \A t \in SUBSET S : (t \subseteq s => \A x \in t : x = FALSE \/ (\A x \in t : x = TRUE /\ s = t))
Boundary(x, y) == (x < 1 \/ x > N \/ y < 1 \/ y > N)
LiveNeighbors(x, y) == Sum({(x', y') \in {(x-1, y-1), (x-1, y), (x-1, y+1), (x, y-1), (x, y+1), (x+1, y-1), (x+1, y), (x+1, y+1)} : ~Boundary(x', y') /\ grid[x', y']})
NextState(x, y) == LET liveCount == LiveNeighbors(x, y)
                   IN  IF grid[x, y] THEN
                           liveCount \in {2, 3}
                       ELSE
                           liveCount = 3

Init == grid \in [1..N -> [1..N -> BOOLEAN]]

Next == /\ \E newGrid \in [1..N -> [1..N -> BOOLEAN]] :
             /\ \A x \in 1..N : \A y \in 1..N : newGrid[x, y] = NextState(x, y)
             /\ grid' = newGrid

Spec == Init /\ [][Next]_<<grid>>
=============================================================================