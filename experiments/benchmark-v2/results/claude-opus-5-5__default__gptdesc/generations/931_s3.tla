---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache-annotated version of the HourClock specification.              *)
(* It duplicates SpecifyingSystems/HourClock/HourClock.tla so that the     *)
(* modules in the Liveness chapter can EXTEND HourClock from a sibling     *)
(* module.                                                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

vars == << hr >>

(***************************************************************************)
(* Initial state: the hour hand shows some hour from 1 to 12.              *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

(***************************************************************************)
(* Next-state action: the hour advances by one, wrapping from 12 to 1.     *)
(***************************************************************************)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(***************************************************************************)
(* The complete specification.                                             *)
(***************************************************************************)
HC == HCini /\ [][HCnxt]_hr

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK == hr \in (1 .. 12)

THEOREM HC => []HCini
=============================================================================