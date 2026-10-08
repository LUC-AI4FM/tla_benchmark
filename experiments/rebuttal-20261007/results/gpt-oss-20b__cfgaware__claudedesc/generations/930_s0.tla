------------------------------ MODULE Clock12 ------------------------------
VARIABLE hr

(* --- Initial condition: hour must be in 1..12 --- *)
HCini == hr \in 1..12

(* --- Next-state relation: advance hour by one with wrap-around --- *)
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

(* --- Stuttering step: hour unchanged --- *)
Stutter == hr' = hr

(* --- Full specification: initial condition and stuttering-tolerant next action --- *)
HC == HCini /\ [] ( HCnxt \/ Stutter )

THEOREM HC_implies_invariant == HC => [] HCini
=============================================================================