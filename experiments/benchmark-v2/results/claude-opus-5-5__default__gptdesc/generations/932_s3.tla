---------------------------- MODULE APLiveHourClock ----------------------------
(***************************************************************************)
(* A type-annotated wrapper for the LiveHourClock specification.           *)
(* Its only purpose is to give Apalache a type for the variable hr.        *)
(* All definitions come from LiveHourClock, which is instantiated with     *)
(* this module's hr substituted for its own hr.                            *)
(***************************************************************************)

VARIABLES
    \* @type: Int;
    hr

INSTANCE LiveHourClock

(***************************************************************************)
(* Aliases for the instantiated definitions. They add no new behavior.     *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == LSpec
=============================================================================