------------------------------- MODULE MultiSlotConsensus -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Slots, Values

VARIABLES proposedValues, chosenValues

Init == /\ proposedValues = {}
        /\ chosenValues \in [Slots -> {}]

Next ==
    \/ /\ E v \notin proposedValues
       /\ proposedValues' = proposedValues \cup {v}
       /\ chosenValues' = chosenValues
    \/ /\ E s \in Slots
       /\ chosenValues[s] = {}
       /\ E v \in proposedValues
       /\ chosenValues' = [chosenValues EXCEPT ![s] = {v}]
       /\ proposedValues' = proposedValues

Spec ==
    /\ Init
    /\ [][Next]_<<proposedValues, chosenValues>>
    /\ WF_next(<<proposedValues, chosenValues>>)

TypeOK ==
    /\ proposedValues \subseteq Values
    /\ (\A s \in Slots: chosenValues[s] \subseteq Values)
    /\ (\A s \in Slots: Cardinality(chosenValues[s]) \leq 1)

Nontrivial ==
    \/ proposedValues = {}
    \/ (\E s \in Slots: chosenValues[s] /= {})

Stability ==
    /\ (\A v \notin proposedValues: [][v \notin proposedValues]_<<proposedValues, chosenValues>>)
    /\ (\A s \in Slots, v \in Values: <>(chosenValues[s] = {v}) => []<>(chosenValues[s] = {v}))

PerSlotConsistency ==
    (\A s \in Slots: <>[](\E v \in proposedValues: chosenValues[s] = {v}))

Liveness ==
    WF_next(<<proposedValues, chosenValues>>) -> <>(\A s \in Slots: chosenValues[s] /= {})

=============================================================================