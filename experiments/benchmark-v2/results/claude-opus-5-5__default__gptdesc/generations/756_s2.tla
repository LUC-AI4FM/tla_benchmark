---------------------------- MODULE APDieHarder ------------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the DieHarder specification.  It gives    *)
(* type annotations for the constants and the variable, instantiates       *)
(* DieHarder, and defines concrete constant values (JugVal, CapacityVal,   *)
(* GoalVal) for use with APDieHarder.cfg.                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Set(Str);
    Jug,
    \* @type: Str -> Int;
    Capacity,
    \* @type: Int;
    Goal

VARIABLES
    \* @type: Str -> Int;
    contents

vars == << contents >>

DH == INSTANCE DieHarder

(***************************************************************************)
(* Concrete constant values for Apalache. These are bound in               *)
(* APDieHarder.cfg, e.g. Jug <- JugVal, Capacity <- CapacityVal.           *)
(***************************************************************************)
JugVal == {"j1", "j2"}

CapacityVal == [j \in JugVal |-> IF j = "j1" THEN 3 ELSE 5]

GoalVal == 4

(***************************************************************************)
(* Initial predicate, next-state relation and specification, taken from    *)
(* the instantiated DieHarder module.                                      *)
(***************************************************************************)
Init == DH!Init

Next == DH!Next

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeOK == DH!TypeOK

NotSolved == DH!NotSolved

==============================================================================