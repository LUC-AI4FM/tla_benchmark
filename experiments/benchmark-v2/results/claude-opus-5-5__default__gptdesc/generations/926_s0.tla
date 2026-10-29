-------------------------- MODULE APHourClock2 --------------------------
(***************************************************************************)
(* Apalache type annotations for HourClock2.tla, applied via INSTANCE so   *)
(* that the original specification remains separate and unmodified.       *)
(*                                                                         *)
(* HourClock2 is an alternative formulation of HourClock that computes the *)
(* next hour as (hr % 12) + 1 instead of using an IF-THEN-ELSE.            *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* The current hour shown on the clock.
    \* @type: Int;
    hr

INSTANCE HourClock2

(***************************************************************************)
(* Convenience aliases for the definitions imported from HourClock2.       *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

TypeOK == hr \in 1..12

THEOREM Spec => []TypeOK
=============================================================================