---- MODULE ModCycle ----
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

-----------------------------------------------------------------------------
\* Helper predicates over the cycling state

\* State predicate: the current value is 1
IsOne == x = 1

\* State predicate: all work is considered done once x reaches 2
Done == x = 2

\* Action predicate: a transition that wraps from 2 back to 0
Wrap == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
\* Type invariant

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
\* Initial state and next-state relation

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

Inv == TypeOK

\* Each step either stutters or advances x modulo 3
StepProperty == [][x' = (x + 1) % 3]_vars

-----------------------------------------------------------------------------
\* TLC-specific check of named-state coverage information.
\* Inspects coverage data obtained through TLCGet and asserts that the
\* three named predicates (IsOne, Done, Wrap) are each counted exactly once.

NamedPredicates == {"IsOne", "Done", "Wrap"}

CoverageCheck ==
    LET cov == TLCGet("stats")
    IN  /\ Assert(\A p \in NamedPredicates : p \in DOMAIN cov.named,
                  "Missing named predicate in coverage information")
        /\ Assert(\A p \in NamedPredicates : cov.named[p] = 1,
                  "Named predicate not counted exactly once")

PostCondition == CoverageCheck

=============================================================================