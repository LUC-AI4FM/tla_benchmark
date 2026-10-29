--------------------------- MODULE ApaCoffeeCan ---------------------------
(***************************************************************************)
(* Thin wrapper around the CoffeeCan specification that adds the type     *)
(* annotations required by the Apalache model checker. The original       *)
(* CoffeeCan specification is kept separate and unchanged.                 *)
(*                                                                         *)
(* This module defines no local behavior. The algorithm dynamics come     *)
(* from the instantiated CoffeeCan module. These include Init, Next,      *)
(* Spec, the actions, the invariants and the temporal properties.         *)
(***************************************************************************)

CONSTANT
    \* Maximum number of beans the can may hold.
    \* @type: Int;
    MaxBeanCount

VARIABLE
    \* The can, recording the counts of black and white beans.
    \* @type: [black: Int, white: Int];
    can

(***************************************************************************)
(* Import all definitions of CoffeeCan. The constant MaxBeanCount and the *)
(* variable can are substituted implicitly by the identically named       *)
(* declarations above.                                                    *)
(***************************************************************************)
INSTANCE CoffeeCan

=============================================================================