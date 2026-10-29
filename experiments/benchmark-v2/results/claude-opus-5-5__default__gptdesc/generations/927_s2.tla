---- MODULE APHourClock ----
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.             *)
(* HourClock is reused through INSTANCE, so HourClock.tla stays unchanged. *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for the definitions inherited from HourClock, so that tools    *)
(* can use the standard entry points.                                     *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

(* Safety invariant: the type invariant inherited from HourClock *)
TypeOK == HCini

====