---------------------------- MODULE APDieHarder ------------------------------
(***************************************************************************)
(* Apalache-specific type annotations and concrete constant values for an  *)
(* instance of the DieHarder specification. Used with APDieHarder.cfg.    *)
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

DH == INSTANCE DieHarder

\* Re-exported definitions from the DieHarder instance
TypeOK    == DH!TypeOK
Init      == DH!Init
Next      == DH!Next
Spec      == DH!Spec
NotSolved == DH!NotSolved

\* Concrete constant values, see APDieHarder.cfg
JugVal == {"j1", "j2"}

CapacityVal == [j \in JugVal |-> IF j = "j1" THEN 3 ELSE 5]

==============================================================================