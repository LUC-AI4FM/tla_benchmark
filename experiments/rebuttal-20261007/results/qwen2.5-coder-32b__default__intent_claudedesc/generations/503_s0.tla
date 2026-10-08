------------------------------- MODULE Consensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Candidates

VARIABLES Chosen

Init == /\ Chosen = {}
        /\ Chosen \subseteq Candidates
        /\ Cardinality(Chosen) <= 1

Next ==
    \/ /\ Chosen = {}
       /\ \E v \in Candidates : ['][Chosen'] = {v}]
    \/ /\ Chosen /= {}

Spec == Init /\ [][Next]_<<Chosen>>

SafetyInvariant ==
    /\ Chosen \subseteq Candidates
    /\ Cardinality(Chosen) <= 1

LivenessProperty ==
    <>[] (\E v \in Candidates : Chosen' = {v})

FairSpec ==
    Spec /\ WF_next(<<Chosen>>)

THEOREM Spec => []SafetyInvariant

THEOREM FairSpec => LivenessProperty
=============================================================================