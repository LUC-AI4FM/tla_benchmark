MODULE Demo

EXTENDS Naturals, SETS

CONSTANTS Op

VARIABLE x

Init == x = 0

Next == \E v' \in Op(x) : x' = v'

Spec == Init /\ [][Next]_x

(* Local operator that ignores its argument and returns the powerset of a fixed finite set S *)
S == {1, 2}

LocalPowSetOp(z) == \power S

(* In a configuration file, one could override Op with LocalPowSetOp:
   CONSTANT Op = LocalPowSetOp
*)