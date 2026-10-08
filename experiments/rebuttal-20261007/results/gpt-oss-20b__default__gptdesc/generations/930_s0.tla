MODULE SimpleClock
EXTENDS Naturals

VARIABLES hr

(* --- Initialization --- *)
Init == hr \in 1..12

(* --- Next-state action --- *)
Next ==
    /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
    /\ UNCHANGED <<>>

(* --- Specification --- *)
Spec == Init /\ [][Next]_hr

(* --- Invariant --- *)
HCini == hr \in 1..12

THEOREM Clock_Invariant ==
    Spec => [] HCini

===============================================================================