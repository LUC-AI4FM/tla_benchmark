------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLE x

(* --- initialization --- *)
Init == 
  x = 1

(* --- next-state relation --- *)
Next ==
  \/ (x < 5) /\ x' = x + 1
  \/ (x = 5) /\ x' = x

(* --- safety invariants --- *)
SafeInv    == [] (x <= 5)
StutterInv == [] (x = 5 -> X(x = 5))

(* --- liveness property --- *)
LivenessProp == <> (x = 5)

Spec == Init /\ [][Next]_x /\ WF/Next
=============================================================================