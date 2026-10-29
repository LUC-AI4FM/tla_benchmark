---------------------------- MODULE MCSession3proj ----------------------------
(***************************************************************************)
(* Model-checking companion module for Session3proj.                       *)
(* Provides concrete integer sets used as substitutions for the constant   *)
(* parameter sets MSet and NSet of the underlying specification.           *)
(* This version is self-contained so that it parses on its own.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS MSet, NSet

VARIABLES m, n

vars == <<m, n>>

(***************************************************************************)
(* Concrete set-valued definitions used to instantiate the parameters.     *)
(***************************************************************************)
ConstMSet == {1, 2, 3}

ConstNSet == {1, 2}

(***************************************************************************)
(* Minimal stand-in behavior for the underlying Session3proj spec:         *)
(* pick an element of each parameter set and allow re-choosing.            *)
(***************************************************************************)
Init ==
    /\ m \in MSet
    /\ n \in NSet

Next ==
    /\ m' \in MSet
    /\ n' \in NSet

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ m \in MSet
    /\ n \in NSet
================================================================================