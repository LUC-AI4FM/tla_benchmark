---------------------------- MODULE ApaCoffeeCan ----------------------------
(***************************************************************************)
(* A thin wrapper around the CoffeeCan specification that adds the type    *)
(* annotations required by the Apalache model checker. The original       *)
(* CoffeeCan specification is kept unchanged and separate.                 *)
(*                                                                         *)
(* This module defines no algorithm dynamics of its own. Init, Next, Spec, *)
(* the type invariant, the safety invariants, the liveness properties and  *)
(* the fairness conditions are all imported unchanged from CoffeeCan       *)
(* through the unnamed INSTANCE statement below. CONSTANT MaxBeanCount and *)
(* VARIABLE can are substituted implicitly by name.                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* Maximum number of beans the can may hold.
    \* @type: Int;
    MaxBeanCount

VARIABLE
    \* Number of black and white beans currently in the can.
    \* @type: [black: Int, white: Int];
    can

(***************************************************************************)
(* Import every definition of CoffeeCan, including Init, Next, Spec and    *)
(* its properties. No local behavior is added here.                        *)
(***************************************************************************)
INSTANCE CoffeeCan

=============================================================================