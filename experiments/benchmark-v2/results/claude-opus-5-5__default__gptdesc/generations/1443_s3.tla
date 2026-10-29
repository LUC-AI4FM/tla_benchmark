---------------------------- MODULE CycleMod3 ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* Initial state and transition relation *)

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper predicates *)

\* State predicate: the state is 1
IsOne == x = 1

\* State predicate: all work is considered done at 2
AllDone == x = 2

\* Action predicate: a transition wraps from 2 back to 0
Wrap == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* TLC-specific check of named-state coverage information *)

NamedPredicates == {"IsOne", "AllDone", "Wrap"}

\* Coverage information that TLC exposes through TLCGet.
Coverage == TLCGet("stats")

\* Each of the three named predicates is counted exactly once.
CoverageCheck ==
    /\ "coverage" \in DOMAIN Coverage
    /\ \A p \in NamedPredicates :
          /\ p \in DOMAIN Coverage.coverage
          /\ Coverage.coverage[p] = 1

PostCondition == CoverageCheck

=============================================================================