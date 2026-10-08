------------------------------- MODULE Consensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Processes,  \* Set of processes
    Values      \* Set of possible values

VARIABLES 
    proposals,  \* Set of proposed values
    chosen       \* The chosen value (or << >> if no value is chosen)

Init == /\ proposals = {}
        /\ chosen = << >>

Next ==
    \/ /\ \/ \E v \in Values : proposals' = proposals \cup {v}
           /\ chosen' = chosen
       /\ \/ chosen = << >>
          /\ \E v \in proposals : chosen' = v
             /\ proposals' = proposals
       /\ \/ chosen /= << >>
          /\ proposals' = proposals
          /\ chosen' = chosen

Spec ==
    /\ Init
    /\ [][Next]_<<proposals, chosen>>
    /\ WF_next(<<proposals, chosen>>)

\* Safety properties
Validity == \A v \in Values : \/ chosen = << >> \/ chosen = v
Agreement == \/ chosen = << >> \/ (\A v1, v2 \in Values : v1 = v2 \/ chosen # v1 \/ chosen # v2)
Integrity == \/ chosen = << >> \/ \A s \in State: s.chosen = chosen

\* Liveness properties
EventualChoice ==
    <>(\E v \in Values : chosen = v)

Nontriviality ==
    <>[](\A v \in Values : v \notin proposals) -> <>(\E v \in Values : chosen = v)

State == [proposals: SUBSET Values, chosen: (Values \cup {<< >>})]

=============================================================================