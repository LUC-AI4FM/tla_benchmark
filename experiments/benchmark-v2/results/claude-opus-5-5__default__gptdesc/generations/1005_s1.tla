--------------------------- MODULE APAbcastFolklore ---------------------------
(***************************************************************************)
(* Thin wrapper that supplies Apalache type annotations for the           *)
(* specification bcastFolklore.  The original specification is kept free  *)
(* of tool-specific annotations; this module only declares typed         *)
(* constants and variables and instantiates bcastFolklore with them.     *)
(* It introduces no behavior of its own: Init, Next and Spec are taken    *)
(* directly from the instantiated module.                                 *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F

VARIABLES
    \* @type: Set(Int);
    Corr,
    \* @type: Int;
    nCrashed,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,
    \* @type: Set(<<Int, Str>>);
    sent

vars == << Corr, nCrashed, pc, rcvd, sent >>

\* Instantiate the original, annotation-free specification.
BF == INSTANCE bcastFolklore

\* No new behavior is defined here; everything is delegated to bcastFolklore.
Init == BF!Init

Next == BF!Next

Spec == Init /\ [][Next]_vars

================================================================================