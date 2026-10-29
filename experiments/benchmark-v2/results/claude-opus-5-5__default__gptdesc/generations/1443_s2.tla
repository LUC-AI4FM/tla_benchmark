---------------------------- MODULE ModCycle ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* State machine *)

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper predicates *)

\* The state is 1.
IsOne == x = 1

\* All work is considered done when the state is 2.
AllDone == x = 2

\* A transition that wraps from 2 back to 0.
Wraps == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
(* Safety invariant *)

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* TLC-specific check: inspect named-state coverage information through   *)
(* TLCGet and assert that each of the three named predicates is counted    *)
(* exactly once.                                                           *)

NamedPredicates == {"IsOne", "AllDone", "Wraps"}

CoverageCheck ==
    LET cov == TLCGet("stats").named
    IN  /\ DOMAIN cov \supseteq NamedPredicates
        /\ \A p \in NamedPredicates : cov[p] = 1

PostCondition == CoverageCheck

=============================================================================