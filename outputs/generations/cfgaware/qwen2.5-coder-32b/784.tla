------------------------------- MODULE ConwayLife -------------------------------

CONSTANTS N

VARIABLE grid

(*--algorithm ConwayLife
variables grid = [x \in 1..N, y \in 1..N -> FALSE];
begin
    while TRUE do
        with newGrid == [x \in 1..N, y \in 1..N |-> NextState(x, y)];
        grid := newGrid;
    end while;
end algorithm*)

NextState(x, y) ==
    LET liveNeighbors == LiveNeighborCount(x, y)
    IN CASE grid[x, y] = TRUE /\ (liveNeighbors = 2 \/ liveNeighbors = 3) -> TRUE
       [] grid[x, y] = FALSE /\ liveNeighbors = 3 -> TRUE
       [] OTHER -> FALSE

LiveNeighborCount(x, y) ==
    LET neighbors == {(x-1, y-1), (x-1, y), (x-1, y+1),
                      (x, y-1),         (x, y+1),
                      (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN Sum({(nx, ny) \in neighbors | IsValid(nx, ny)}, LAMBDA p: IF grid[p[1], p[2]] THEN 1 ELSE 0)

IsValid(x, y) ==
    x >= 1 /\ x <= N /\ y >= 1 /\ y <= N

Sum(S, f) ==
    CHOOSE s \in SUBSET S : Cardinality(s) = Cardinality(S)
    \o (IF s = {} THEN 0 ELSE LET e == CHOOSE v \in s : TRUE
                               IN f[e] + Sum(s \ {e}, f))

TypeOK ==
    /\ N \in Nat
    /\ N > 0
    /\ grid \in [1..N -> [1..N -> BOOLEAN]]

Init ==
    grid = [x \in 1..N, y \in 1..N -> FALSE]

Next ==
    /\ \E newGrid \in [1..N -> [1..N -> BOOLEAN]]:
        /\ grid' = newGrid
        /\ \A x \in 1..N, y \in 1..N: newGrid[x, y] = NextState(x, y)

Spec ==
    Init /\ [][Next]_<<grid>>

===============================================================================