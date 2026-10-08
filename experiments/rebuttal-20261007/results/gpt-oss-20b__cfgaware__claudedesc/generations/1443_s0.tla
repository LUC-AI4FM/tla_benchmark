------------------------------ MODULE CounterTest ------------------------------
IMPORTING TLC

VARIABLE x

(* Predicates for possibility coverage *)
AllDone == x = 2
AtOne   == x = 1
WrapAround == /\ x = 2
              /\ ((x + 1) Mod 3) = 0

(* Next-state relation: cyclic counter modulo 3 *)
Next ==
  LET newX == (x + 1) Mod 3 IN
    /\ x' = newX

Init == x = 0

Spec == Init /\ [][Next]_x

_POSSIBLE AllDone
_POSSIBLE AtOne
_POSSIBLE WrapAround

PossibleCounts ==
  LET stats == TLCGet("all:named") IN
    /\ stats[AllDone]   = 1
    /\ stats[AtOne]     = 1
    /\ stats[WrapAround] = 1

=============================================================================