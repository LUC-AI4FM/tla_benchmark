---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* A thin wrapper around the HourClock specification that adds Apalache   *)
(* type annotations while leaving the original HourClock module           *)
(* unchanged. It declares the single state variable hr, annotated with    *)
(* an integer type, and instantiates HourClock. It defines no behavior of *)
(* its own: the definitions below are aliases for the operators imported  *)
(* from HourClock, so that sibling modules can refer to HourClock-related *)
(* content without modifying the original source.                        *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock

(***************************************************************************)
(* Aliases for the imported HourClock definitions (no new behavior).      *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

TypeOK == HCini

=============================================================================