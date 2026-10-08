MODULE HC2
EXTENDS HourClock

VARIABLES hr

(* Initial condition inherited from HourClock *)
Init == HCini

(* Alternative next-state action *)
HCnxt2 ==
  hr' = ((hr Mod 12) + 1)

(* Specification using the alternative next-state action *)
Spec == Init /\ [][HCnxt2]_hr

THEOREM HC_equiv_HC2 ==
  HC = Spec

===============================================================================