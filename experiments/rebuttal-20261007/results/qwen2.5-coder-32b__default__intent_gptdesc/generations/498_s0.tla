------------------------------- MODULE MultiInstanceConsensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

VARIABLES proposals, decisions

Init == /\ proposals = [s \in Slots |-> {}]
        /\ decisions = [s \in Slots |-> <<>>]

Next ==
    \/ \E s \in Slots, v \in Values : proposals' = [proposals EXCEPT ![s] = proposals[s] \cup {v}]
    \/ \E s \in Slots, v \in proposals[s], decisions[s] = <<>> :
        decisions' = [decisions EXCEPT ![s] = <<v>>]

Spec ==
    /\ Init
    /\ [][Next]_<<proposals, decisions>>
    /\ WF_next(<<proposals, decisions>>)

TypeOK ==
    /\ \A s \in Slots : proposals[s] \subseteq Values
    /\ \A s \in Slots : decisions[s] \in {<<>>, <<v>> | v \in Values}

Safety ==
    /\ \A s \in Slots : decisions[s] = <<>> \/ decisions[s][1] \in proposals[s]
    /\ \A s \in Slots : Cardinality({decisions[s][1] | decisions[s] /= <<>>}) <= 1

Liveness ==
    /\ \A s \in Slots, v \in Values :
        WF_next(<<proposals, decisions>>) -> <>[](decisions[s] = <<v>>)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => <>([]Liveness)
=============================================================================