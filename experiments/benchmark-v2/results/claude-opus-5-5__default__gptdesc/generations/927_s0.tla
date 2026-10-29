---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.  The         *)
(* original HourClock.tla file is left unchanged: this module declares     *)
(* the variable hr with its type annotation and instantiates HourClock.    *)
(* HourClock defines HCini, HCnxt and HC, so this module inherits them.    *)
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

(***************************************************************************)
(* Type invariant: the hour is always between 1 and 12.                    *)
(***************************************************************************)
TypeInvariant == hr \in 1..12

THEOREM Spec => []TypeInvariant
=============================================================================