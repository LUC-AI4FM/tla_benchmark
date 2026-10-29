---------------------------- MODULE InstanceTest ----------------------------
(***************************************************************************)
(* A small test module that exercises subtle INSTANCE-related semantics   *)
(* (priming, ENABLED, and disjunction of actions) without an actual       *)
(* INSTANCE declaration. It models a single-variable state machine over u.*)
(***************************************************************************)
EXTENDS Naturals

VARIABLE u

vars == << u >>

(***************************************************************************)
(* G is parameterized by a value a and an action A. It is the disjunction  *)
(* of the supplied action with an assignment of a to u.                    *)
(***************************************************************************)
G(a, A) == A \/ (u' = a)

(***************************************************************************)
(* H combines a stuttering assignment on u with an ENABLED test over a     *)
(* disjunctive action formula built from G. The primes inside ENABLED are  *)
(* bound by ENABLED, while the outer u' = u constrains the actual step.    *)
(***************************************************************************)
H == /\ u' = u
     /\ ENABLED (G(u + 1, u' = u) \/ G(u, u' = u + 1))

(***************************************************************************)
(* Minimal scaffolding so the module can be model checked.                 *)
(***************************************************************************)
Init == u = 0

Next == H

Spec == Init /\ [][Next]_vars

TypeOK == u \in Nat

=============================================================================