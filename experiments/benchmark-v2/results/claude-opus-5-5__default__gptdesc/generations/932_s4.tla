-------------------------- MODULE APLiveHourClock --------------------------
(***************************************************************************)
(* A type-annotated wrapper for the LiveHourClock specification.           *)
(*                                                                         *)
(* This module only adds an Apalache type annotation for the variable hr.  *)
(* It defines no operators or properties of its own. Instead, it           *)
(* instantiates LiveHourClock and substitutes its own hr for the hr of     *)
(* LiveHourClock (implicit substitution hr <- hr).                         *)
(*                                                                         *)
(* All definitions of LiveHourClock, and of HourClock which it extends,    *)
(* become available here through the INSTANCE. This includes the initial   *)
(* predicate, the next-state action, the specification, the weak fairness  *)
(* condition, and the safety and liveness properties.                      *)
(***************************************************************************)

VARIABLES
    \* @type: Int;
    hr

INSTANCE LiveHourClock

=============================================================================