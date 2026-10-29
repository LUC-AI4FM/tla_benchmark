------------------------------- MODULE APAEWD840 -------------------------------
(***************************************************************************)
(* Wrapper around EWD840 that adds Apalache type annotations to the       *)
(* constant and variables while leaving the original module unchanged.    *)
(* Init, Next, Spec, the invariants and the liveness properties all come  *)
(* from EWD840 through the INSTANCE statement below.                      *)
(***************************************************************************)
EXTENDS Naturals

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
================================================================================