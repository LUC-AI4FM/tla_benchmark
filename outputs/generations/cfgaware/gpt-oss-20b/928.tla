------------------------------ MODULE HC2 ------------------------------
EXTENDS HourClock

(* Next-state action for alternative hour-clock *)
HCnxt2 == hr' = (hr Mod 12) + 1

(* Alternative specification *)
HC2 == HCini /\ []HCnxt2

THEOREM HC_eq_HC2 == HC <=> HC2
============================================================