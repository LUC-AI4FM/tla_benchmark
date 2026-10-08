---------------------------- MODULE MultiInstanceConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Values, Slots
VARIABLE proposedValues, chosenValues

TypeInvariant == 
  /\ proposedValues \in SUBSET Values
  /\ chosenValues \in [Slots -> SUBSET Values]

Init ==
  /\ proposedValues = {}
  /\ chosenValues = [s \in Slots |-> {}]

Propose(v) == 
  /\ v \in Values
  /\ proposedValues' = proposedValues \cup {v}
  /\ UNCHANGED chosenValues

ChooseSlot(s, v) == 
  /\ s \in Slots
  /\ v \in proposedValues
  /\ chosenValues' = [chosenValues EXCEPT ![s] = {v}]
  /\ UNCHANGED proposedValues

Next ==
  \/ \E v \in Values : Propose(v)
  \/ \E s \in Slots : 
      \E v \in proposedValues : ChooseSlot(s, v)

Spec == Init /\ [][Next]_<<proposedValues, chosenValues>>

LiveSpec == Spec /\ WF_<<proposedValues, chosenValues>>(Next)

THEOREM Spec => []TypeInvariant
THEOREM LiveSpec => <>[]\A s \in Slots : chosenValues[s] /= {}
=============================================================================