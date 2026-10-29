------------------------------ MODULE InstanceSemanticsTest ------------------------------
(***************************************************************************)
(* A small test module that exercises subtle INSTANCE-related semantics    *)
(* (priming, ENABLED, and disjunction of actions). It contains no INSTANCE *)
(* declaration. It models a single-variable state machine over u.          *)
(*                                                                         *)
(* The description says the original file has no Init, Next, or Spec.     *)
(* The minimal Init / Next / Spec below exist only so the module is a      *)
(* complete specification. The core content is the operators G and H.     *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE u

vars == <<u>>

(***************************************************************************)
(* G is parameterized by a value x and an action A. It is the disjunction  *)
(* of the action A with the action that assigns x to u.                     *)
(***************************************************************************)
G(x, A) == A \/ (u' = x)

(***************************************************************************)
(* H combines a stuttering assignment on u (u' = u) with an ENABLED test   *)
(* over a disjunctive action formula built from G. The arguments include   *)
(* primed expressions, so substitution happens under ENABLED. This is the  *)
(* subtle case that INSTANCE semantics must handle correctly.              *)
(***************************************************************************)
H == /\ u' = u
     /\ ENABLED G(u', u' = u + 1)

(***************************************************************************)
(* A second variant that uses an unprimed value argument, for comparison. *)
(***************************************************************************)
H2 == /\ u' = u
      /\ ENABLED G(u, (u' = 1) \/ (u' = u))

(***************************************************************************)
(* Minimal scaffolding                                                      *)
(***************************************************************************)
Init == u = 0

Next == H \/ H2

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety                                                                   *)
(***************************************************************************)
TypeOK == u \in Nat

\* Every Next step is a stuttering step, so u keeps its initial value.
Unchanged == u = 0

THEOREM Spec => [](TypeOK /\ Unchanged)
==========================================================================================