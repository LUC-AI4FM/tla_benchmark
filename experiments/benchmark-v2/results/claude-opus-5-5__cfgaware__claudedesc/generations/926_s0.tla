---------------------------- MODULE APHourClock2 ----------------------------
(***************************************************************************)
(* Type annotations for the hour clock specification, so that it can be    *)
(* checked with Apalache while the original specification stays free of   *)
(* tool-specific syntax.                                                   *)
(*                                                                         *)
(* HourClock2 is an alternative formulation of the hour clock. It computes *)
(* the next hour with modular arithmetic, (hr % 12) + 1, instead of an     *)
(* IF/THEN/ELSE. Its definitions are written inline here, so the module is *)
(* self-contained.                                                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

\* The hour is always between 1 and 12.
HCini == hr \in (1 .. 12)

\* The hour advances by one and wraps from 12 back to 1.
HCnxt2 == hr' = (hr % 12) + 1

\* Temporal specification: start in a valid hour, then advance or stutter.
HC2 == HCini /\ [][HCnxt2]_hr

-----------------------------------------------------------------------------
(* The conditional formulation from HourClock, used to state equivalence. *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC <=> HC2

THEOREM HC2 => []HCini
=============================================================================