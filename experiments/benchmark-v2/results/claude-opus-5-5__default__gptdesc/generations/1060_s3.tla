-------------------------------- MODULE APAEWD840 --------------------------------
(***************************************************************************)
(* A wrapper around the EWD840 specification that adds Apalache type      *)
(* annotations to its constant and variables. The original EWD840 module  *)
(* is left unchanged.                                                      *)
(*                                                                         *)
(* This module defines no operators of its own. The unparameterized        *)
(* INSTANCE below imports every definition of EWD840 into this module      *)
(* under its original name. That includes Init, Next and Spec, and all of  *)
(* EWD840's invariants, liveness properties and fairness conditions.       *)
(* Defining them again here would cause SANY "multiply-defined" errors.    *)
(***************************************************************************)

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

==================================================================================