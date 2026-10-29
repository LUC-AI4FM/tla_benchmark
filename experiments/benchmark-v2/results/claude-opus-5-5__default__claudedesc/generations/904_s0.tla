---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper around the HourClock specification so that it    *)
(* can be checked with Apalache. The original HourClock specification is   *)
(* kept free of tool-specific annotations; the annotation for the variable *)
(* hr lives here.                                                          *)
(*                                                                         *)
(* Model-checking configuration:                                           *)
(*   SPECIFICATION HC                                                      *)
(*   INVARIANT     HCini                                                   *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

    ---------------------------- MODULE HourClock ----------------------------
    (***********************************************************************)
    (* The underlying hour clock specification. It is declared here as an *)
    (* inner module so that this file is self-contained.                  *)
    (***********************************************************************)
    EXTENDS Naturals
    VARIABLE hr

    HCini == hr \in (1 .. 12)

    HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

    HC == HCini /\ [][HCnxt]_hr
    --------------------------------------------------------------------------
    THEOREM HC => []HCini
    ==========================================================================