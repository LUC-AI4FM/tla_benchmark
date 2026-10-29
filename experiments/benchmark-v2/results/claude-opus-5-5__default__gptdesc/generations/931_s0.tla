---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* This module provides Apalache type annotations for the                  *)
(* Liveness/HourClock.tla specification.  It duplicates                    *)
(* SpecifyingSystems/HourClock/HourClock.tla, but is kept separate so      *)
(* that other modules (such as those in the Liveness chapter) can EXTEND   *)
(* HourClock from a sibling module.  The module introduces a single        *)
(* variable hr, annotated for Apalache as an integer.  The behavior is     *)
(* that of the standard hour clock.                                        *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

vars == <<hr>>

(***************************************************************************)
(* Hour clock definitions (as in HourClock.tla)                            *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Standard names for Init / Next / Spec                                   *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety: the clock always shows a valid hour.                            *)
(***************************************************************************)
TypeOK == hr \in (1 .. 12)

THEOREM HC => []HCini
THEOREM Spec => []TypeOK
=============================================================================