------------------------------- MODULE Consensus -------------------------------

CONSTANTS Candidates

VARIABLES chosen

(*--algorithm Consensus
variables chosen \in SUBSET Candidates;

begin
    Init == chosen = {}

    Next ==
        \/ /\ chosen = {}
           /\ \E v \in Candidates : chosen' = {v}
        \/ chosen' = chosen

    Spec == Init /\ [][Next]_<<chosen>>

    InvChosenSubsetCandidates == chosen \subseteq Candidates
    InvChosenFinite == Finite(chosen)
    InvChosenAtMostOne == Cardinality(chosen) <= 1

    SafetyInvariant ==
        InvChosenSubsetCandidates /\ InvChosenFinite /\ InvChosenAtMostOne

    LiveSpec == Spec /\ WF_next(Next)

end algorithm *)

THEOREM Spec => []SafetyInvariant
THEOREM LiveSpec => <>[](\E v \in Candidates : chosen = {v})

=============================================================================