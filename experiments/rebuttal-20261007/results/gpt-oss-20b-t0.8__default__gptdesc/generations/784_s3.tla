--------------------------- MODULE Life ----------------------------
EXTENDS Integers

CONSTANT N

VARIABLES grid

Coords == { <<i,j>> \mid i \in 1..N /\ j \in 1..N }

InGrid(i, j) == (1 <= i /\ i <= N /\ 1 <= j /\ j <= N)

CountLiveNeighbors(p) ==
  LET i == p[1] ; j == p[2]
  IN \sum di \in {-1,0,1} :
        \sum dj \in {-1,0,1} :
          IF (di = 0 /\ dj = 0) THEN 0
          ELSE IF InGrid(i + di, j + dj)
                THEN IF grid[ <<i+di,j+dj>> ] THEN 1 ELSE 0
                ELSE 0

Next ==
  /\ \A pos \in Coords:
        LET n == CountLiveNeighbors(pos) IN
            IF grid[pos] THEN
                grid'[pos] = (n = 2 \/ n = 3)
            ELSE
                grid'[pos] = (n = 3)

Init == /\ grid \in [ Coords -> {TRUE, FALSE} ]

Spec == Init /\ [] (Next \/ (grid' = grid))

=============================================================================