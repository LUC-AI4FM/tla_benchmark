---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.             *)
(* INSTANCE is used so that the original HourClock.tla file does not need *)
(* to be modified.                                                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases to the definitions inherited from HourClock (HCini, HCnxt, HC). *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

(***************************************************************************)
(* Safety invariant: the hour is always in 1..12.                          *)
(***************************************************************************)
TypeOK == hr \in (1 .. 12)

THEOREM Spec => []TypeOK
=============================================================================