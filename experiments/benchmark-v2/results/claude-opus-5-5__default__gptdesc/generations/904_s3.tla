---------------------------- MODULE HourClockTyped ----------------------------
(***************************************************************************)
(* Thin wrapper around the HourClock specification that adds Apalache    *)
(* type annotations while leaving the original HourClock module          *)
(* unchanged. Sibling chapter modules can refer to this module to get    *)
(* the HourClock content. It adds no behavior, actions or properties of  *)
(* its own. Init, Next and Spec are only aliases for HourClock's         *)
(* definitions.                                                          *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for HourClock's definitions. They add no new behavior.        *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

==============================================================================