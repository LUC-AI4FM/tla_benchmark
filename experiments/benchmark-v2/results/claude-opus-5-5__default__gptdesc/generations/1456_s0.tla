---------------------------- MODULE NamedStates ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS ExpectedFullSet, ExpectedGainThree

VARIABLES x, y

vars == <<x, y>>

S == {1, 2, 3}

\* Initial state: both x and y are arbitrary subsets of S
Init ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

\* Next-state relation: y is left unchanged, and the next value of x
\* is constrained to be a subset of y'
Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

\* Provided only to satisfy the required module structure. The described
\* system has no fairness condition.
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

\* State predicate: x is the full set {1, 2, 3}
FullSet == x = {1, 2, 3}

\* Action predicate: element 3 is gained in a transition
GainThree == 3 \notin x /\ 3 \in x'

\* Named-predicate exploration metadata, read through TLCGet.
\* TLCGet(name) is expected to return the count TLC recorded for the
\* named predicate.
FullSetCount   == TLCGet("FullSet")
GainThreeCount == TLCGet("GainThree")

\* Assertions on the expected counts for the named predicates.
\* Use this as a POSTCONDITION in the TLC configuration.
CountsOK ==
    /\ Assert(FullSetCount = ExpectedFullSet,
              <<"Unexpected FullSet count", FullSetCount>>)
    /\ Assert(GainThreeCount = ExpectedGainThree,
              <<"Unexpected GainThree count", GainThreeCount>>)

\* Sanity check on general exploration statistics.
\* All 8 * 8 = 64 combinations of x and y are initial states, so they
\* are all reachable.
StatsOK ==
    Assert(TLCGet("stats").distinct = 64,
           <<"Unexpected number of distinct states", TLCGet("stats").distinct>>)

=============================================================================