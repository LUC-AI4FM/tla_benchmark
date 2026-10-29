---------------------------- MODULE ApaCoffeeCan ----------------------------
(***************************************************************************)
(* A thin wrapper around the CoffeeCan specification that adds the type   *)
(* annotations needed by the Apalache model checker. The original          *)
(* CoffeeCan specification stays separate and unchanged.                   *)
(*                                                                         *)
(* This module defines no algorithm dynamics, actions or temporal          *)
(* properties of its own. All of them (Init, Next, Spec, the type          *)
(* invariant, the safety and liveness properties, and the fairness         *)
(* conditions) come from the unnamed INSTANCE of CoffeeCan below. That     *)
(* instance brings every CoffeeCan definition into this module's           *)
(* namespace, with the same names.                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* The maximum number of beans the can may hold.
    \* @type: Int;
    MaxBeanCount

VARIABLES
    \* The coffee can, as a record of black and white bean counts.
    \* @type: [black: Int, white: Int];
    can

(***************************************************************************)
(* Import the original specification. The constant MaxBeanCount and the    *)
(* variable can are substituted implicitly, because they have the same     *)
(* names here.                                                             *)
(***************************************************************************)
INSTANCE CoffeeCan

=============================================================================