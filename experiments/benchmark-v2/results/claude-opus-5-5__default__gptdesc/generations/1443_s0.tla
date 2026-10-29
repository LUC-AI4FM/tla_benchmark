---------------------------- MODULE ModCounter ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
\* Initial state: x starts at 0
Init == x = 0

\* Each step advances x modulo 3, cycling through 0, 1, 2
Next == x' = (x + 1) % 3

\* Temporal specification: initial state, then Next steps with stuttering
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Helper predicates

\* State predicate: the state is 1
IsOne == x = 1

\* State predicate: all work is considered done at 2
AllDone == x = 2

\* Action predicate: a transition that wraps from 2 back to 0
Wrap == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK == x \in 0..2

\* Every Next step either increments by one or wraps from 2 to 0
StepShape == [][ (x' = x + 1) \/ Wrap ]_vars

-----------------------------------------------------------------------------
\* TLC-specific check: inspect named-state coverage information obtained
\* through TLCGet and assert that each of the three named predicates is
\* counted exactly once.

NamedPredicates == {"IsOne", "AllDone", "Wrap"}

CoverageInfo == TLCGet("coverage")

CoverageCheck ==
    /\ NamedPredicates \subseteq DOMAIN CoverageInfo
    /\ \A n \in NamedPredicates : CoverageInfo[n] = 1

PostCondition ==
    Assert(CoverageCheck,
           "Expected each named predicate IsOne, AllDone and Wrap to be counted once")

=============================================================================