```
MODULE MinimalTwoStateSystem
EXTENDS Integers, Sequences, Strings

CONSTANTS 

VARIABLES pc, history

Init ==
  /\ pc = "A"
  /\ history = << >>

Next ==
  \/ (pc = "A") /\ (pc' = "B") /\ (history' = Append(history, "A"))
  \/ (pc = "B") /\ (pc' = "A") /\ (history' = history)

Spec ==
  Init /\ [][Next]_<<pc, history>> /\ WF_<<pc, history>>(Next)

Constraint ==
  Len(history) < 3

Prop ==
  <> (pc = "Done")

THEOREM Spec => []Constraint => Prop
```