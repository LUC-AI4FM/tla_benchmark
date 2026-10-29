------------------------------ MODULE NamedSubsetStates ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Universe

ASSUME Universe = {1, 2, 3}

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ y \in SUBSET Universe
    /\ x \in SUBSET Universe
    /\ x \subseteq y

Init ==
    /\ y \in SUBSET Universe
    /\ x \in SUBSET y

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------------------
\* Named predicates

\* State predicate: x is the full set {1, 2, 3}.
FullSet == x = {1, 2, 3}

\* Action predicate: element 3 is gained in a transition.
GainThree == 3 \notin x /\ 3 \in x'

----------------------------------------------------------------------------------------
\* Expected counts, computed directly from the model.

AllStates ==
    { <<a, b>> \in (SUBSET Universe) \X (SUBSET Universe) : a \subseteq b }

AllTransitions ==
    { <<s, t>> \in AllStates \X AllStates :
        /\ t[2] = s[2]
        /\ t[1] \subseteq t[2] }

FullSetStates ==
    { s \in AllStates : s[1] = {1, 2, 3} }

GainThreeTransitions ==
    { tr \in AllTransitions : 3 \notin tr[1][1] /\ 3 \in tr[2][1] }

ExpectedDistinctStates == 27
ExpectedFullSetCount   == 1
ExpectedGainThreeCount == 25

ASSUME Cardinality(AllStates) = ExpectedDistinctStates
ASSUME Cardinality(FullSetStates) = ExpectedFullSetCount
ASSUME Cardinality(GainThreeTransitions) = ExpectedGainThreeCount

----------------------------------------------------------------------------------------
\* Inspect TLC's exploration metadata after model checking.

PostCondition ==
    LET stats == TLCGet("stats")
    IN  /\ stats.distinct = ExpectedDistinctStates
        /\ Cardinality(FullSetStates) = ExpectedFullSetCount
        /\ Cardinality(GainThreeTransitions) = ExpectedGainThreeCount

----------------------------------------------------------------------------------------
\* Safety invariants

Inv == TypeOK

SubsetInv == x \subseteq y

YConstant == [][y' = y]_vars

=========================================================================================