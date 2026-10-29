---------------------------- MODULE HourClock_typed ----------------------------
(***************************************************************************)
(* A thin companion wrapper around the HourClock specification that adds   *)
(* Apalache type annotations, leaving the original HourClock module        *)
(* unchanged.  The definitions below are those of HourClock, reproduced    *)
(* here (equivalent to INSTANCE HourClock) so that this module is          *)
(* self-contained and binds to the model-checking configuration.           *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

\* Initial predicate: the hour displayed is between 1 and 12.
HCini == hr \in (1 .. 12)

\* Next-state relation: advance the hour, wrapping from 12 to 1.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* The complete specification of the hour clock.
HC == HCini /\ [][HCnxt]_hr

--------------------------------------------------------------------------------
THEOREM HC => []HCini
================================================================================