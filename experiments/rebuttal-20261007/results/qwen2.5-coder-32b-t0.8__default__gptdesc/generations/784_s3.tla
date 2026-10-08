```tla
MODULE ConwayLife

EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLE grid

(*--algorithm ConwaysGameOfLife
variables grid = [x \in 1..N, y \in 1..N |-> FALSE];
begin
    Init;
    while TRUE do
        await TRUE;
        Next;
    end while
end algorithm*)

Sum(S) == SUM {grid[x][y] : <<x, y>> \in S}

IsLive(x, y) == 
    IF x > 0 /\ x <= N /\ y > 0 /\ y <= N THEN grid[x][y]
    ELSE FALSE

CountLiveNeighbors(x, y) ==
    LET neighbors == {(x-1, y-1), (x-1, y), (x-1, y+1),
                       (x, y-1),           (x, y+1),
                       (x+1, y-1), (x+1, y), (x+1, y+1)}
    IN  Sum({<<a, b>> \in neighbors : IsLive(a, b)})

Init == 
    /\ grid \in [1..N -> [1..N -> BOOLEAN]]

Next ==
    LET nextGrid == [x \in 1..N, y \in 1..N |-> 
        LET liveNeighbors == CountLiveNeighbors(x, y)
        IN  CASE liveNeighbors = 3 \/ (liveNeighbors = 2 /\ grid[x][y])
            -> TRUE
            [] OTHER -> FALSE]
    IN  /\ UNCHANGED <<>>
        /\ grid' = nextGrid

Spec ==
    Init /\ [][Next]_<<>>

====

```