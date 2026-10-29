---------------------------- MODULE NamedStates ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Elems
ASSUME Elems = {1, 2, 3}

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in SUBSET Elems
    /\ y \in SUBSET Elems

Init ==
    /\ y \in SUBSET Elems
    /\ x \in SUBSET y

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

\* Named state predicate: x is the full set {1, 2, 3}
FullSet == x = {1, 2, 3}

\* Named action predicate: element 3 is gained in a transition
GainThree == 3 \notin x /\ 3 \in x'

\* Safety invariants
Inv == x \subseteq y
YConst == y \in SUBSET Elems

\* -------------------------------------------------------------------------
\* Expected counts, computed from the state space.
\* Reachable states are the pairs (x, y) with x \subseteq y \subseteq Elems.
\* -------------------------------------------------------------------------
States == { <<a, b>> \in (SUBSET Elems) \X (SUBSET Elems) : a \subseteq b }

FullSetStates == { s \in States : s[1] = {1, 2, 3} }

GainThreeSteps ==
    { <<s, t>> \in States \X States :
        /\ t[2] = s[2]
        /\ 3 \notin s[1]
        /\ 3 \in t[1] }

ExpectedDistinct  == 27
ExpectedFullSet   == 1
ExpectedGainThree == 25

ASSUME Cardinality(States)         = ExpectedDistinct
ASSUME Cardinality(FullSetStates)  = ExpectedFullSet
ASSUME Cardinality(GainThreeSteps) = ExpectedGainThree

\* Inspect the exploration metadata recorded by TLC once checking finishes.
PostCondition ==
    LET stats == TLCGet("stats")
    IN  /\ Assert(stats.distinct = ExpectedDistinct,
                  <<"Unexpected number of distinct states", stats.distinct>>)
        /\ Assert(Cardinality(FullSetStates) = ExpectedFullSet,
                  <<"Unexpected FullSet count", Cardinality(FullSetStates)>>)
        /\ Assert(Cardinality(GainThreeSteps) = ExpectedGainThree,
                  <<"Unexpected GainThree count", Cardinality(GainThreeSteps)>>)

\* No full temporal formula and no fairness: TLC is configured with
\* INIT Init and NEXT Next. Spec is the plain safety formula.
Spec == Init /\ [][Next]_vars

=============================================================================