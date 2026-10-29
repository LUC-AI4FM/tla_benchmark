---------------------------- MODULE APAHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper around the HourClock specification so that the   *)
(* Apalache model checker can process it, while the original HourClock     *)
(* module stays free of tool-specific annotations.                         *)
(*                                                                         *)
(* In the original setup this module reads:                                *)
(*                                                                         *)
(*     VARIABLE \* @type: Int;                                             *)
(*              hr                                                         *)
(*     INSTANCE HourClock                                                  *)
(*                                                                         *)
(* The definitions of HourClock (Specifying Systems, Chapter 2) are        *)
(* reproduced below so that this module parses as a standalone module.    *)
(*                                                                         *)
(* Model-checking configuration:                                           *)
(*     SPECIFICATION HC                                                    *)
(*     INVARIANT     HCini                                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

-----------------------------------------------------------------------------
(* Definitions inherited from HourClock *)

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(* Standard aliases *)

Init == HCini

Next == HCnxt

Spec == HC

-----------------------------------------------------------------------------
(* Safety: the clock always shows a valid hour. *)

TypeOK == hr \in (1 .. 12)

HCiniInvariant == HCini

THEOREM HC => []HCini
=============================================================================