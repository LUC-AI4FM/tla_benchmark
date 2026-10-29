---------------------------- MODULE ApaCoffeeCan ----------------------------
(***************************************************************************)
(* A thin wrapper around the CoffeeCan specification that adds the type    *)
(* annotations needed by the Apalache model checker. The original          *)
(* specification is kept separate and unannotated.                         *)
(*                                                                         *)
(* This module declares only the constant and the variable, with their    *)
(* Apalache types. It defines no behavior of its own. Init, Next, Spec,    *)
(* the type invariant, the safety invariants, the liveness properties and  *)
(* the fairness conditions all come from CoffeeCan through the INSTANCE    *)
(* statement below.                                                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* The maximum number of beans the can may hold.
    \* @type: Int;
    MaxBeanCount

VARIABLE
    \* The can, holding a number of black beans and a number of white beans.
    \* @type: [black: Int, white: Int];
    can

-----------------------------------------------------------------------------
(***************************************************************************)
(* Import every definition of the original specification. MaxBeanCount    *)
(* and can are substituted implicitly by the identically named constant    *)
(* and variable declared above.                                            *)
(***************************************************************************)
INSTANCE CoffeeCan

=============================================================================