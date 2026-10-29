---------------------------- MODULE APDieHarder ----------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the DieHarder specification. Declares    *)
(* typed constants and variables, instantiates DieHarder, and provides     *)
(* concrete constant values (JugVal, CapacityVal) for APDieHarder.cfg.     *)
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

DH == INSTANCE DieHarder WITH Jug <- Jug,
                              Capacity <- Capacity,
                              Goal <- Goal,
                              contents <- contents

(***************************************************************************)
(* Concrete constant values used by APDieHarder.cfg                        *)
(***************************************************************************)
JugVal == {"j1", "j2"}

CapacityVal == [ j \in JugVal |-> IF j = "j1" THEN 3 ELSE 5 ]

GoalVal == 4

(***************************************************************************)
(* Behavior, lifted from the DieHarder instance                            *)
(***************************************************************************)
Init == DH!Init

Next == DH!Next

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == DH!TypeOK

\* Violated exactly when some jug holds Goal gallons (the puzzle is solved)
NotSolved == DH!NotSolved

=============================================================================