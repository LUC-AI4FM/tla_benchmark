---------------------------- MODULE APLiveHourClock ----------------------------
(***************************************************************************)
(* A type-annotated wrapper for the LiveHourClock specification.          *)
(* It declares the variable hr with an Apalache type annotation and       *)
(* instantiates LiveHourClock, substituting its own hr for the one in     *)
(* LiveHourClock. The behavior, invariants, liveness properties and       *)
(* fairness conditions are all inherited from LiveHourClock.              *)
(***************************************************************************)

VARIABLES
    \* @type: Int;
    hr

INSTANCE LiveHourClock WITH hr <- hr

(***************************************************************************)
(* Aliases for the specification components inherited from LiveHourClock *)
(* and HourClock. No new behavior is defined here.                        *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == LSpec

=============================================================================