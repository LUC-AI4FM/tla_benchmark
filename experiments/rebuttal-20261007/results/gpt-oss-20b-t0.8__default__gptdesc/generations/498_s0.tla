MODULE MultiSlotConsensus
EXTENDS Naturals

CONSTANTS SlotSet, ValueSet

VARIABLE proposedValues, chosenSlots

vars == <<proposedValues, chosenSlots>>

Init ==
    /\ proposedValues = {}
    /\ chosenSlots = [s \in SlotSet |-> {}]

Propose ==
    /\ ∃ v ∈ ValueSet : v ∉ proposedValues
    /\ proposedValues' = proposedValues ∪ {v}
    /\ chosenSlots' = chosenSlots

Choose ==
    /\ ∃ s ∈ SlotSet : chosenSlots[s] = {}
    /\ LET newChosen == [chosenSlots EXCEPT ![s] = {v}]
       IN
           /\ v ∈ proposedValues
           /\ chosenSlots' = newChosen
           /\ proposedValues' = proposedValues

Next == Propose \/ Choose

TypeInv ==
    /\ proposedValues ⊆ ValueSet
    /\ chosenSlots \in [SlotSet -> SUBSET ValueSet]
    /\ ∀ s ∈ DOMAIN(chosenSlots) :
        (chosenSlots[s] = {}) \/ ((#chosenSlots[s] = 1) /\ ∀ v ∈ chosenSlots[s] : v ∈ proposedValues)

Spec ==
    Init /\ [][Next]_vars /\ WF(Next) /\ ∀ s ∈ SlotSet : <> (chosenSlots[s] \= {})
