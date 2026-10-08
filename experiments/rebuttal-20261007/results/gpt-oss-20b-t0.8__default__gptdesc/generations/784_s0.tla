MODULE Life
EXTENDS Naturals, Sequences

CONSTANT N  \* Size of the board (N x N)

(* --- Definitions of sets and helper operators -------------------------------- *)

Board == { <<i,j>> | i \in 1..N /\ j \in 1..N }

Offsets == { <<-1,-1>>, <<-1,0>>, <<-1,1>>,
             <<0,-1>>,           <<0,1>>,
             <<1,-1>>,  <<1,0>>,  <<1,1>> }

OffsetAdd == \lambda p, o : <<p[1]+o[1], p[2]+o[2]>>

Neighbors == \lambda p : { OffsetAdd(p,o) : o \in Offsets }

CountLiveNeighbors == \lambda g, p :
    LET sum = \sum_{q \in Neighbors(p)} IF q \in Board
                                            THEN (IF g[q] THEN 1 ELSE 0)
                                            ELSE 0
    IN sum

NewState == \lambda g, p :
    LET n = CountLiveNeighbors(g,p)
    IN IF g[p] /\ (n = 2 \/ n = 3) THEN TRUE
       ELSE IF ~g[p] /\ n = 3 THEN TRUE
       ELSE FALSE

(* --- State variables -------------------------------------------------------- *)

VARIABLE grid

(* --- Initial condition ----------------------------------------------------- *)

Init == /\ grid \in Board -> BOOLEAN

(* --- Next-state relation --------------------------------------------------- *)

Next ==
    /\ grid' \in Board -> BOOLEAN
    /\ \A p \in Board : grid'[p] = NewState(grid, p)

(* --- Temporal specification ------------------------------------------------ *)

Spec == Init /\ [][Next]_grid

END MODULE