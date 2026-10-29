---------------------------- MODULE ModThreeCycle ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

-----------------------------------------------------------------------------
(* Type correctness *)
TypeOK == x \in {0, 1, 2}

(* Initial state *)
Init == x = 0

(* Advance modulo 3 *)
Next == x' = (x + 1) % 3

(* Temporal specification: initial state, then Next steps or stuttering *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper predicates *)

\* The state in which x is 1.
IsOne == x = 1

\* All work is considered done when x reaches 2.
AllDone == x = 2

\* A transition that wraps from 2 back to 0.
Wraps == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
(* Safety invariants *)

Inv == TypeOK

-----------------------------------------------------------------------------
(* TLC-specific check: inspect named-state coverage information through
   TLCGet and assert that each of the three named predicates is counted
   exactly once. Intended for use as a POSTCONDITION. *)

NamedPredicates == {"IsOne", "AllDone", "Wraps"}

CoverageCheck ==
    LET cov == TLCGet("spec")["named"]
    IN  /\ \A p \in NamedPredicates :
              /\ p \in DOMAIN cov
              /\ cov[p] = 1
        /\ Assert(\A p \in NamedPredicates : cov[p] = 1,
                  "Each named predicate must be counted exactly once")

=============================================================================