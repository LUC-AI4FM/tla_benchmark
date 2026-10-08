------------------------------ MODULE HourClock2 ------------------------------
EXTENDS HourClock

(* Alternative next-state relation *)
HCnxt2 == hr' = (hr Mod 12) + 1

(* Alternative specification *)
HC2 == HCini /\ [][HCnxt2]_hr

(* Re-export original specification for configuration *)
HC == HourClock.HC

THEOREM HC_Equiv_HC2 == HC <=> HC2
=============================================================================