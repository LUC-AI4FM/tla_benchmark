---------------------------- MODULE EnabledSubst ----------------------------
EXTENDS Naturals

VARIABLES u, v

vars == <<u, v>>

(***************************************************************************)
(* G takes a variable x and an action A.  It checks whether the composite  *)
(* action is enabled.  The composite action is the disjunction of:         *)
(*   - the passed-in action A,                                             *)
(*   - a stuttering-like step on the passed variable x,                    *)
(*   - a swap-like step between the variables u and v.                     *)
(* When G is called with x = u, the module-level variable u appears both   *)
(* as the substituted parameter and as a free variable in the body.        *)
(***************************************************************************)
G(x, A) == ENABLED (A \/ x' = x \/ (u' = v /\ v' = u))

(***************************************************************************)
(* H combines a constraint that v stays unchanged with an invocation of G  *)
(* in which the actual arguments mention u and the primed variable u'.     *)
(***************************************************************************)
H == /\ v' = v
     /\ G(u, u' = v)

Init == /\ u \in 0..2
        /\ v \in 0..2

Next == \/ /\ u' = (u + 1) % 3
           /\ H
        \/ /\ u' = v
           /\ v' = u

Spec == Init /\ [][Next]_vars

TypeOK == /\ u \in 0..2
          /\ v \in 0..2

(***************************************************************************)
(* By the semantics of ENABLED, G(u, u' = v) is always TRUE, since the     *)
(* disjunct u' = u (and also u' = v) can always be satisfied by some       *)
(* choice of primed values.                                                *)
(***************************************************************************)
GAlwaysEnabled == G(u, u' = v)

EnabledInv == GAlwaysEnabled

EnabledH == ENABLED H
=============================================================================