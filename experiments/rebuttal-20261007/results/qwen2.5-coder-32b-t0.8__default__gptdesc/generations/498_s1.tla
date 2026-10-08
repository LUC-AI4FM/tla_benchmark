---- MODULE MultiSlotConsensus ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Slots, Values

VARIABLES proposedValues, chosenValues

Init == /\ proposedValues = {}
          /\ \A s \in Slots: chosenValues[s] = {}

Next ==
    \/ /\ E \notin DOMAIN proposedValues
       /\ \E v \in Values: proposedValues' = [proposedValues EXCEPT ![E] = {v}]
          /\ chosenValues' = chosenValues
    \/ /\ \E s \in Slots: chosenValues[s] = {}
       /\ \E v \in DOMAIN proposedValues: chosenValues' = [chosenValues EXCEPT ![s] = {v}]
          /\ proposedValues' = proposedValues

TypeInvariant ==
    /\ proposedValues \subseteq [DOMAIN Values -> Pow(Values)]
    /\ \A s \in Slots: chosenValues[s] \in { {}, Pow(Values) }

Nontriviality ==
    \/ \E v \in DOMAIN proposedValues
    \/ \E s \in Slots, v \in DOMAIN proposedValues: chosenValues[s] = {v}

Stability ==
    /\ \A v \in DOMAIN proposedValues, s1, s2 \in Slots:
        chosenValues'[s1] = {v} => chosenValues'[s2] = chosenValues[s2]
    /\ \A v \in DOMAIN proposedValues, s \in Slots:
        chosenValues[s] = {} => chosenValues'[s] = chosenValues[s]

PerSlotConsistency ==
    /\ \A s \in Slots: Cardinality(chosenValues[s]) <= 1

Spec ==
    /\ Init
    /\ [][Next]_<<proposedValues, chosenValues>>
    /\ WF_next(<<proposedValues, chosenValues>>)

Liveness ==
    \/ \A s \in Slots: <>(\E v \in DOMAIN proposedValues: chosenValues[s] = {v})

====