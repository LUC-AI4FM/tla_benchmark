--------------------------- MODULE APCoffeeCan ---------------------------
(***************************************************************************)
(* A thin wrapper around the CoffeeCan specification that adds             *)
(* Apalache-oriented type annotations. The original CoffeeCan module is    *)
(* kept free of these annotations.                                         *)
(*                                                                         *)
(* This module defines no dynamics of its own. Init, Next, Spec, the       *)
(* actions, the safety invariants, the liveness properties and the         *)
(* fairness conditions all come from CoffeeCan through the INSTANCE        *)
(* statement below.                                                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* The maximum number of beans the can may hold.
    \* @type: Int;
    MaxBeanCount

VARIABLE
    \* The contents of the can: the number of black beans and the
    \* number of white beans.
    \* @type: [black: Int, white: Int];
    can

(***************************************************************************)
(* Import every definition of CoffeeCan. The constant MaxBeanCount and the *)
(* variable can are substituted implicitly by name.                        *)
(***************************************************************************)
INSTANCE CoffeeCan

=============================================================================