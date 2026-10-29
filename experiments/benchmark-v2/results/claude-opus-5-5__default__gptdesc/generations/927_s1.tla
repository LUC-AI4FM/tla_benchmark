------------------------------ MODULE APHourClock ------------------------------
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.             *)
(* The module uses INSTANCE so that the original HourClock.tla does not    *)
(* need to be modified. It declares the variable hr and gives it the type  *)
(* Int in an Apalache type comment.                                        *)
(*                                                                         *)
(* A copy of HourClock is included as an inner module so that this file    *)
(* parses on its own. It is placed before the outer VARIABLES declaration  *)
(* so that its own declaration of hr does not clash with the outer one.    *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------------ MODULE HourClock ------------------------------
  VARIABLE hr

  HCini == hr \in (1 .. 12)

  HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

  HC == HCini /\ [][HCnxt]_hr
  ------------------------------------------------------------------------------
  THEOREM HC => []HCini
  ==============================================================================