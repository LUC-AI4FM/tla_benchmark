---------------------------- MODULE APAHourClock2 ----------------------------
(***************************************************************************)
(* Apalache type annotations for HourClock2.tla.                           *)
(*                                                                         *)
(* This module is a thin wrapper that applies Apalache type annotations to *)
(* HourClock2.tla via INSTANCE, keeping the original specification         *)
(* separate and unmodified.                                                *)
(*                                                                         *)
(* HourClock2 is an alternative formulation of HourClock.  Its next-state *)
(* relation uses (hr % 12) + 1 instead of an IF-THEN-ELSE.                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

(***************************************************************************)
(* Instantiate the original specification.  The unnamed INSTANCE imports   *)
(* HCini, HCnxt and HC, with HourClock2's hr bound to this module's hr.    *)
(***************************************************************************)
INSTANCE HourClock2

(***************************************************************************)
(* The required top-level names are aliases for the instantiated           *)
(* definitions.  They add no behavior of their own.                        *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_hr

(***************************************************************************)
(* Safety invariant: the clock always shows an hour between 1 and 12.      *)
(***************************************************************************)
TypeInvariant == hr \in 1..12

=============================================================================