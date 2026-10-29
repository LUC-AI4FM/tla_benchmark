------------------------------- MODULE InstanceSemanticsTest -------------------------------
(***************************************************************************)
(* A small test module that exercises subtle action-level semantics       *)
(* related to INSTANCE substitution (priming, ENABLED, and disjunction of *)
(* actions), without containing an actual INSTANCE declaration.           *)
(*                                                                         *)
(* The original module defines only the variable u and the operators G    *)
(* and H. The Init, Next, Spec and TypeOK definitions at the end are       *)
(* minimal additions so that the module has a complete specification.     *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE u

vars == <<u>>

(***************************************************************************)
(* G is parameterized by a value v and an action A. It is the disjunction  *)
(* of the action A with an action that sets u to v.                        *)
(***************************************************************************)
G(v, A) == A \/ (u' = v)

(***************************************************************************)
(* H combines a stuttering assignment on u with an ENABLED test over a     *)
(* disjunctive action formula built from G. Inside ENABLED, primed         *)
(* occurrences of u are existentially quantified, while unprimed           *)
(* occurrences refer to the current state.                                 *)
(***************************************************************************)
H == /\ u' = u
     /\ ENABLED G(u + 1, u' = u)

(***************************************************************************)
(* Minimal additions so that the module has a complete specification.      *)
(***************************************************************************)
Init == u = 0

Next == H

Spec == Init /\ [][Next]_vars

TypeOK == u \in Nat

=============================================================================