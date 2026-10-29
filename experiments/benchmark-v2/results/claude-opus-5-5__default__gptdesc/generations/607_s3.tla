---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* TLC model-checking wrapper for the MultiUser specification.            *)
(* This module defines no state variables or actions of its own: the      *)
(* VARIABLES, Init, Next and Spec all come from the extended MultiUser    *)
(* module.  It only supplies a constant-valued operator for the model     *)
(* parameter (user identifiers) and gathers the refinement properties     *)
(* expressed through the instances SingleUser2, SingleUser3 and           *)
(* SingleUserP(p) that MultiUser declares.                                *)
(* MultiUser.tla must be on the same path for SANY to resolve EXTENDS.    *)
(***************************************************************************)
EXTENDS MultiUser, TLC

\* CONSTANT definitions @modelParameterConstants:0Users
const_17385913267612000 ==
    1..2
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_17385913267612001 ==
    SingleUser2!Spec
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_17385913267612002 ==
    SingleUser3!Spec
----

\* PROPERTY definition @modelCorrectnessProperties:2
prop_17385913267612003 ==
    SingleUserP(2)!Spec
----

\* PROPERTY definition @modelCorrectnessProperties:3
prop_17385913267612004 ==
    \A p \in {2} : SingleUserP(p)!Spec
----

\* PROPERTY definition @modelCorrectnessProperties:4
prop_17385913267612005 ==
    \A p \in {1} : SingleUserP(p)!Spec
----
=============================================================================