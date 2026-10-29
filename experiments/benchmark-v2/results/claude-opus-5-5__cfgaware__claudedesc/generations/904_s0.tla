---------------------------- MODULE MC_HourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper around the HourClock specification, intended to  *)
(* make the spec usable with the Apalache model checker. The variable hr   *)
(* carries an Apalache type annotation. The HourClock definitions are      *)
(* given inline so that this module is self-contained.                     *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

\* Initial predicate: the hour is any valid clock hour (1..12).
HCini == hr \in (1 .. 12)

\* Next-state relation: advance the hour cyclically from 12 back to 1.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* Temporal specification of the hour clock.
HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
THEOREM HC => []HCini
=============================================================================