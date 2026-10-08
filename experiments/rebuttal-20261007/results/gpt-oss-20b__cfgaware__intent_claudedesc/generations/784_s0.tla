------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Naturals

CONSTANT N \in Nat
(* Assume N > 0 *)

VARIABLES grid

State == [pos \in 1..N \times 1..N -> BOOLEAN]

TypeOK == grid \in State

InBounds(i) == 1 <= i /\ i <= N

Offsets == { <<di,dj>> | di \in -1..1 /\ dj \in -1..1 /\ ~(di=0 /\ dj=0) }

neighborCount(p, state) ==
  LET
    i == p[1]
    j == p[2]
  IN
    \sum_{o \in Offsets} IF InBounds(i + o[1]) /\ InBounds(j + o[2])
                         THEN IF state[<<i + o[1], j + o[2]>>] THEN 1 ELSE 0
                         ELSE 0

nextState(p, state) ==
  LET cnt == neighborCount(p,state)
  IN
    IF state[p]
      THEN (cnt = 2 \/ cnt = 3)
      ELSE (cnt = 3)

Init == TypeOK

Next ==
  /\ grid' = [p \in 1..N \times 1..N |-> nextState(p,grid)]

vars == {grid}

Spec == Init /\ [][Next]_vars
=============================================================================