---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* TLC model-checking companion module for the SingleLaneBridge spec.      *)
(* It defines no algorithm, actions, properties, or proofs of its own.     *)
(* VARIABLES, Init, Next, Spec, invariants, liveness properties, and       *)
(* fairness conditions are all inherited from SingleLaneBridge.            *)
(* This module only supplies concrete finite values for its constants.     *)
(***************************************************************************)
EXTENDS SingleLaneBridge

\* CONSTANT definitions @modelParameterConstants:0CarsRight
const_CarsRight ==
    {"r1", "r2"}
----

\* CONSTANT definitions @modelParameterConstants:1CarsLeft
const_CarsLeft ==
    {"l1", "l2"}
----

\* CONSTANT definitions @modelParameterConstants:2Bridge
const_Bridge ==
    {4, 5}
----

\* CONSTANT definitions @modelParameterConstants:3Positions
const_Positions ==
    1..8
----

=============================================================================