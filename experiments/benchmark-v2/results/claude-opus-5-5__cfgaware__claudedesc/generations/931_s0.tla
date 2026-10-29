---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper around the HourClock specification so that the  *)
(* Apalache model checker can process it, while the original HourClock     *)
(* module stays free of tool-specific annotations.                         *)
(*                                                                         *)
(* The HourClock definitions are given inline here so that this module is  *)
(* self-contained. They match the HourClock module from Specifying Systems.*)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

-----------------------------------------------------------------------------
(* Definitions of the HourClock module *)

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
THEOREM HC => []HCini
=============================================================================