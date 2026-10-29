---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache-annotated version of the HourClock specification from         *)
(* "Specifying Systems".  The module is a duplicate of                     *)
(* SpecifyingSystems/HourClock/HourClock.tla.  It is kept separate so that *)
(* modules in the Liveness chapter can EXTEND an hour clock from a sibling *)
(* module.  The single variable hr carries an Apalache type annotation.    *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

vars == << hr >>

TypeOK == hr \in 1..12

HCini == hr \in 1..12

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety: the hour is always a value from 1 to 12.                        *)
(***************************************************************************)
TypeInvariant == TypeOK

THEOREM HC => []HCini

=============================================================================