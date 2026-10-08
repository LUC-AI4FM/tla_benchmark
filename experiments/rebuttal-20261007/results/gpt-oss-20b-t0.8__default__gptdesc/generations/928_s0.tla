MODULE HC2
EXTENDS HourClock

VARIABLES hr

(* Alternative next-state action *)
HCnxt2 == hr' = (hr % 12) + 1

Spec == HCini /\ [] ([HCnxt2]_hr)

THEOREM HC_eq_HC2:
  HC = Spec

===============================================================================