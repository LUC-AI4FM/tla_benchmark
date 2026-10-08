MODULE GameOfLife
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES grid

(* Helper functions *)
Neighbors(i,j) == { <<p,q>> \in DOMAIN [1..N][1..N] :
                    (Abs(p-i) <= 1 /\ Abs(q-j) <= 1) /\ ~(p=i /\ q=j) }

NeighborCount(i,j) ==
    Sum(<<p,q>> \in Neighbors(i,j),
        IF grid[p][q] THEN 1 ELSE 0)

NextCell(i,j) ==
    LET n == NeighborCount(i,j) IN
    IF grid[i][j]
       THEN (n = 2 \/ n = 3)
       ELSE (n = 3)

Init == /\ grid \in [1..N][1..N] -> BOOLEAN

Next ==
    LET newGrid == [i \in 1..N, j \in 1..N |-> NextCell(i,j)] IN
        /\ grid' = newGrid

Spec == Init /\ [][Next]_grid

(* Invariants *)
TypeInvariant == /\ grid \in [1..N][1..N] -> BOOLEAN

===============================================================================