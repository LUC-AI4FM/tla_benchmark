--------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache-annotated copy of the HourClock specification from            *)
(* "Specifying Systems".  It is an exact duplicate of                      *)
(* SpecifyingSystems/HourClock/HourClock.tla.  It is kept separate so that *)
(* modules in the Liveness chapter can EXTEND it from a sibling module.    *)
(* The only addition is the Apalache type annotation on the variable hr.   *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

(***************************************************************************)
(* The behavior of the hour clock, as in HourClock.tla.                    *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Standard names for use with model checkers.                             *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_hr

(***************************************************************************)
(* Safety invariant: the hour is always between 1 and 12.                  *)
(***************************************************************************)
TypeOK == HCini

-----------------------------------------------------------------------------
THEOREM HC => []HCini
=============================================================================