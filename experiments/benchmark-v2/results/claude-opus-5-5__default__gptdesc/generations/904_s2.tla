--------------------------- MODULE HourClockTyped ---------------------------
(***************************************************************************)
(* A thin wrapper around the HourClock specification that adds Apalache   *)
(* type annotations while leaving the original HourClock module           *)
(* unchanged.  It declares the single state variable hr with an integer   *)
(* type annotation and instantiates HourClock.  It adds no new behavior.  *)
(* Init, Next and Spec are aliases for HourClock's own definitions so     *)
(* that sibling modules and model checkers can refer to them.             *)
(***************************************************************************)

VARIABLE
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for the definitions imported from HourClock.  These add no new *)
(* behavior.                                                               *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

(***************************************************************************)
(* The type invariant comes from HourClock: the hour is always in 1..12.  *)
(***************************************************************************)
TypeInvariant == HCini

=============================================================================