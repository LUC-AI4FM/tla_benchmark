------------------------------ MODULE Life ------------------------------
IMPORTS Integers

CONSTANT N

VARIABLES grid

(* Convert a Boolean to an integer *)
LiveVal(b) == IF b THEN 1 ELSE 0

(* Value of cell (i,j), treating out‑of‑bounds as dead *)
AliveAt(i, j) ==
    IF i \in 1..N /\ j \in 1..N
       THEN grid[i][j]
       ELSE FALSE

(* Count live neighbors of cell (i,j) *)
CountNeighbors(i, j) ==
    \sum_{di \in {-1,0,1}} \sum_{dj \in {-1,0,1}}
        IF di = 0 /\ dj = 0 THEN 0
        ELSE LiveVal(AliveAt(i+di, j+dj))

(* Next‑state relation *)
Next ==
    /\ grid' = [i \in 1..N |-> [j \in 1..N |-> 
            LET n == CountNeighbors(i,j)
                alive == AliveAt(i,j) IN
              IF alive THEN (n = 2 \/ n = 3)
                         ELSE (n = 3)]]

(* Type correctness *)
TypeOK ==
    /\ N \in Nat
    /\ N > 0
    /\ grid \in [1..N][1..N] -> BOOLEAN

(* Initial condition: any state satisfying type constraints *)
Init == TypeOK

(* Temporal specification with stuttering allowed *)
Spec == Init /\ [][Next]_{grid}

=============================================================================