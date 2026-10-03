------------------------------ MODULE SimpleClock ------------------------------
EXTENDS Naturals

VARIABLE hr

(* Initial predicate *)
HCini == (hr >= 1 /\ hr <= 12)

(* Next-state action *)
HCnxt == 
    (hr' = IF hr = 12 THEN 1 ELSE hr + 1)

(* Initial state *)
Init == HCini

(* Specification *)
Spec == Init /\ [][HCnxt]_<<hr>>

(* Temporal property *)
HC == Init /\ [] HCnxt

THEOREM Spec => [] HCini
=============================================================================