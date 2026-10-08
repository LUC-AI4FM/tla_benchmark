MODULE TwoStateHistory
EXTENDS Sequences

CONSTANT MaxLen

VARIABLES pc, history

A == "A"
B == "B"

Init ==
  /\ pc = A
  /\ history = <<>>

ActionA ==
  /\ pc = A
  /\ pc' = B
  /\ history' = Append(history, A)

ActionB ==
  /\ pc = B
  /\ pc' = A
  /\ UNCHANGED history

Next == ActionA \/ ActionB

HistoryBound == Len(history) <= MaxLen

Spec == Init
        /\ [][Next]_vars
        /\ WF_vars(ActionA \/ ActionB)
        /\ HistoryBound

LivenessProp == <> (pc = "Done")