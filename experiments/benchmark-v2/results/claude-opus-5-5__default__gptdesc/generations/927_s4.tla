---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.  INSTANCE   *)
(* is used so that the original HourClock.tla file does not need to be    *)
(* modified.                                                               *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for the definitions inherited from HourClock.                   *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

TypeOK == hr \in (1 .. 12)

=============================================================================