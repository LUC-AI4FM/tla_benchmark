---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* TLC model-checking companion module for the SingleLaneBridge spec.      *)
(* It defines no algorithm of its own. It extends SingleLaneBridge and     *)
(* gives concrete values for that module's constants.                      *)
(*                                                                         *)
(* Init, Next, Spec, the invariants, the liveness properties and the       *)
(* fairness conditions are all inherited from SingleLaneBridge. They are   *)
(* not redefined here, because redefining them would be a multiple-        *)
(* definition error in SANY.                                               *)
(*                                                                         *)
(* In the TLC configuration file, substitute the constants as follows:     *)
(*   CONSTANT CarsRight <- const_CarsRight                                 *)
(*   CONSTANT CarsLeft  <- const_CarsLeft                                  *)
(*   CONSTANT Bridge    <- const_Bridge                                    *)
(*   CONSTANT Positions <- const_Positions                                 *)
(*   SPECIFICATION Spec                                                    *)
(***************************************************************************)
EXTENDS SingleLaneBridge, TLC

\* CONSTANT definitions @modelParameterConstants:0CarsRight
const_CarsRight ==
    {"r1", "r2"}
----

\* CONSTANT definitions @modelParameterConstants:1Bridge
const_Bridge ==
    {2, 3, 4}
----

\* CONSTANT definitions @modelParameterConstants:2CarsLeft
const_CarsLeft ==
    {"l1"}
----

\* CONSTANT definitions @modelParameterConstants:3Positions
const_Positions ==
    1..6
----

=============================================================================