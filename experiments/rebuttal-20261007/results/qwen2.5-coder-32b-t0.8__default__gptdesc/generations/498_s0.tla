---------------------------- MODULE MultiSlotConsensus ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS NumSlots

VARIABLES proposedValues, chosenValues

(*--algorithm multi_slot_consensus
variables proposedValues = {}, chosenValues = [slot \in 1..NumSlots |-> {}];

action proposeValue(value)
    with newProposed = proposedValues \cup {value}
    do
        if value \notin proposedValues then
            proposedValues := newProposed;
        end if;
end action;

action chooseValue(slot, value)
    assume slot \in 1..NumSlots /\ value \in proposedValues /\ chosenValues[slot] = {}
    with newChosen = [chosenValues EXCEPT ![slot] = {value}]
    do
        chosenValues := newChosen;
    end action;
end algorithm *)

Init == /\ proposedValues = {}
        /\ chosenValues = [slot \in 1..NumSlots |-> {}]

Next ==
 \/ /\ \/ EXIST value \notin proposedValues :
            /\ proposedValues' = proposedValues \cup {value}
            /\ chosenValues' = chosenValues
    \/ /\ EXIST slot \in 1..NumSlots, value \in proposedValues :
            /\ slot \notin DOMAIN [s \in 1..NumSlots |-> CHOOSE v \in {} : TRUE]
            /\ chosenValues[slot] = {}
            /\ chosenValues' = [chosenValues EXCEPT ![slot] = {value}]
            /\ proposedValues' = proposedValues

Spec == Init /\ [][Next]_<<proposedValues, chosenValues>>

TypeInvariant ==
    /\ proposedValues \subseteq (UNION {S : S \in SUBSET Nat})
    /\ (\A slot \in 1..NumSlots : chosenValues[slot] \in SUBSET Nat)

Nontriviality ==
    \/ proposedValues = {}
    \/ (\E value \in proposedValues : TRUE)

Stability ==
    /\ proposedValues' = proposedValues
    /\ (\A slot \in 1..NumSlots :
        \/ chosenValues'[slot] = chosenValues[slot]
        \/ \/ chosenValues[slot] = {}
           /\ chosenValues'[slot] = {v} \in SUBSET proposedValues)

PerSlotConsistency ==
    \A slot \in 1..NumSlots : Cardinality(chosenValues[slot]) <= 1

Liveness ==
    WF_next(<<proposedValues, chosenValues>>) -> []
        (\E slot \in 1..NumSlots : chosenValues[slot] /= {})_<<proposedValues, chosenValues>>

Theorem == Spec => []TypeInvariant /\ []Nontriviality /\ []Stability /\ []PerSlotConsistency /\ Liveness

=============================================================================