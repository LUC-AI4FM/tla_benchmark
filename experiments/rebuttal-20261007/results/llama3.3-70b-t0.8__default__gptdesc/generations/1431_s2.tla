```
MODULE TwoStateProcess
EXTENDS Integers
CONSTANTS Done
VARIABLES pc, history

Init == (pc = "A") /\ (history = <<>>)

Next == 
  \/ (pc = "A") /\ (pc' = "B") /\ (history' = Append(history, "A")) /\ (action = "A")
  \/ (pc = "B") /\ (pc' = "A") /\ (history' = history) /\ (action = "B")
  \/ (pc' = pc) /\ (history' = history)

Spec == Init /\ [][Next]_<<pc, history>>
          /\ WF_<<action>>(action = "A" \/ action = "B")

HistoryConstraint == Len(history) <= 5

LivenessProperty == <> (pc = "Done")

THEOREM Spec => [] HistoryConstraint
THEOREM Spec => LivenessProperty
```