------------------------------- MODULE InstanceSemanticsTest -------------------------------
EXTENDS Naturals

VARIABLE u

vars == << u >>

-----------------------------------------------------------------------------
(* Helper operator G: parameterized by a value v and an action A.          *)
(* It is the disjunction of the supplied action and an assignment of v     *)
(* to u in the next state.                                                 *)
-----------------------------------------------------------------------------
G(v, A) == A \/ (u' = v)

-----------------------------------------------------------------------------
(* Operator H: a stuttering assignment on u, conjoined with an ENABLED     *)
(* test over a disjunctive action formula built from G. The primes inside  *)
(* the ENABLED refer to the hypothetical next state that ENABLED           *)
(* quantifies over. The u' outside ENABLED refers to the actual step.      *)
-----------------------------------------------------------------------------
H == /\ u' = u
     /\ ENABLED ( G(u, u' = (u + 1) % 3) \/ (u' = u) )

-----------------------------------------------------------------------------
(* Minimal scaffolding so the module can be checked. The original test     *)
(* module concentrates only on the action-level operators above.           *)
-----------------------------------------------------------------------------
Init == u \in 0..2

Next == \/ H
        \/ (G(0, u' = (u + 1) % 3) /\ u' \in 0..2)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)
-----------------------------------------------------------------------------
TypeOK == u \in 0..2

(* H is always enabled, since its ENABLED test contains a stuttering disjunct *)
HAlwaysEnabled == ENABLED H

(* Priming semantics check: H leaves u unchanged *)
HStutters == [][H => (u' = u)]_vars

=============================================================================