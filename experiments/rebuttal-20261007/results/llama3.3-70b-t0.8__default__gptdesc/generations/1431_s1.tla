```
MODULE TwoStateProcess
EXTENDS Integers

CONSTANTS Done

VARIABLES pc, history

Init ==
  /\ pc = "A"
  /\ history = <<>>

Next ==
  \/ pc = "A" /\ action_A
  \/ pc = "B" /\ action_B
  \/ pc' = pc /\ history' = history

action_A ==
  /\ pc = "A"
  /\ pc' = "B"
  /\ history' = Append(history, "A")

action_B ==
  /\ pc = "B"
  /\ pc' = "A"
  /\ history' = history

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(action_A \/ action_B)

vars == <<pc, history>>
Inv == Len(history) <= 10
Liveness == <>[]pc = "Done"

THEOREM Spec => []Inv
THEOREM Spec => Liveness
```