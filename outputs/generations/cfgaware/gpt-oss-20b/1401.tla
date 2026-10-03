------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLE outerX

vars == {outerX}

(* Inner step definition *)
InnerStep ==
  /\ outerX < 3
  /\ outerX' = outerX + 1

Stutter ==
  outerX' = outerX

Next ==
  IF outerX < 3 THEN InnerStep ELSE Stutter

Init ==
  outerX = 0

Spec == Init /\ [][Next]_(vars) /\ WF_vars(InnerStep)

Prop == <> (outerX = 3)

=============================================================================