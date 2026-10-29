---------------------------- MODULE APAHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper around the HourClock specification, intended for *)
(* use with the Apalache model checker.  The single variable hr is         *)
(* annotated with the Int type.  The definitions of HourClock (HCini,      *)
(* HCnxt, HC) are reproduced here, so this module parses on its own. The   *)
(* original pattern is:                                                    *)
(*                                                                         *)
(*     VARIABLE hr                                                         *)
(*     INSTANCE HourClock                                                  *)
(*                                                                         *)
(* Model-checking configuration:                                           *)
(*     SPECIFICATION HC                                                    *)
(*     INVARIANT     HCini                                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* The current hour displayed by the clock.
    \* @type: Int;
    hr

vars == << hr >>

(***************************************************************************)
(* Definitions of the HourClock module.                                    *)
(***************************************************************************)

\* Initial predicate.  It also serves as the type invariant: the hour is
\* always between 1 and 12.
HCini == hr \in (1 .. 12)

\* Next-state relation: advance the hour, wrapping from 12 back to 1.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* The complete temporal specification of the hour clock.
HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Standard aliases.                                                       *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

(***************************************************************************)
(* Safety: the clock never shows an invalid hour.                          *)
(***************************************************************************)
TypeOK == hr \in (1 .. 12)

Inv == HCini

THEOREM HC => []HCini
=============================================================================