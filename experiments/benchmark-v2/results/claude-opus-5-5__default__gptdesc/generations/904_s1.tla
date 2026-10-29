---------------------------- MODULE HourClockTyped ----------------------------
(***************************************************************************)
(* Thin wrapper around the HourClock specification that adds Apalache     *)
(* type annotations without modifying the original HourClock module.      *)
(* It defines no behavior of its own. Init, Next and Spec are aliases     *)
(* for the definitions imported from HourClock.                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for the instantiated HourClock definitions. No new behavior.   *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

=============================================================================