---------------------------- MODULE APLiveHourClock ----------------------------
(***************************************************************************)
(* A type-annotated wrapper for the LiveHourClock specification.           *)
(* Its only purpose is to give Apalache a type annotation for the          *)
(* variable hr. The INSTANCE substitutes this module's hr for the hr of    *)
(* LiveHourClock. All definitions (HCini, HCnxt, HC, LSpec, AlwaysTick,    *)
(* AllTimes, ...) are imported unchanged from LiveHourClock.               *)
(***************************************************************************)

VARIABLES
    \* @type: Int;
    hr

INSTANCE LiveHourClock WITH hr <- hr

(***************************************************************************)
(* Convenience aliases for the imported definitions. These add no new      *)
(* behavior and only give tools standard entry points.                     *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == LSpec

=============================================================================