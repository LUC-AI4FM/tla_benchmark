------------------------------ MODULE APAEWD840 ------------------------------
(***************************************************************************)
(* A lightweight wrapper around EWD840 that adds Apalache type annotations *)
(* to the constants and variables, leaving the original module unchanged. *)
(* Init, Next, Spec, the invariants, the liveness properties and the       *)
(* fairness conditions all come from EWD840 through the INSTANCE below.    *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Str;
    color,
    \* @type: Int;
    tpos,
    \* @type: Str;
    tcolor

INSTANCE EWD840

=============================================================================