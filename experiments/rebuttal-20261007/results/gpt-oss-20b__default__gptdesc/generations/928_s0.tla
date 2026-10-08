MODULE HC2
EXTENDS HourClock

(* Next-state action for hour clock *)
HCnxt2 == hr' = (hr % 12) + 1

(* Initial condition inherited from HourClock *)
Init == HCini

(* Next action *)
Next == HCnxt2

(* Specification *)
Spec == Init /\ [] [Next]_hr

(* Alternative specification using HCini and HCnxt2 *)
HC2 == HCini /\ [] [HCnxt2]_hr

THEOREM HC_eq_HC2 == HC = HC2
=============================================================================