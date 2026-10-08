------------------------------ MODULE ConwayLife ------------------------------
EXTENDS FiniteSets, Integers

CONSTANTS N
ASSUME N > 0

VARIABLES grid

(* --algorithm ConwayLife
variables grid = [x \in 1..N, y \in 1..N |-> FALSE];
begin
    while TRUE do
        with
            nextGrid == [x \in 1..N, y \in 1..N |-> NextState(x, y, grid)];
        do
            grid := nextGrid;
        od;
end algorithm *)

Sum(S) == CHOOSE s: SUBSET S : s = {} /\ SUM s = 0 \/ \E e \in s: SUM s = (SUM (s \ {e}) + IF e THEN 1 ELSE 0)
Boundary(x, y) == x < 1 \/ x > N \/ y < 1 \/ y > N
LiveNeighbors(x, y, g) == Sum({g[x' - 1][y' - 1] : x' \in {x-1..x+1}, y' \in {y-1..y+1} EXCEPT <<x,y>>})
NextState(x, y, g) == LET liveNeighbors == LiveNeighbors(x, y, g)
                      IN (g[x][y] /\ (liveNeighbors = 2 \/ liveNeighbors = 3)) \/ (\neg g[x][y] /\ liveNeighbors = 3)

Init == grid \in [1..N -> [1..N -> BOOLEAN]]

Next == /\ \/ \E x \in 1..N, y \in 1..N: grid' = [grid EXCEPT ![x][y] = NextState(x, y, grid)]
          \/ grid' = grid

Spec == Init /\ [][Next]_<<grid>>
=============================================================================