```
MODULE TwoStateProcess
EXTENDS Integers
CONSTANTS Done
VARIABLES pc, history

Init == (pc = "A") /\ (history = <<>>)

Next == 
  \/ (pc = "A") /\ (pc' = "B") /\ (history' = Append(history, "A")) 
  \/ (pc = "B") /\ (pc' = "A") /\ (history' = history)
  \/ (pc' = pc) /\ (history' = history)

Spec == Init /\ [][Next]_vars
          /\ WF_vars(A \/ B)
          
A == (pc = "A") /\ (pc' = "B") /\ (history' = Append(history, "A"))
B == (pc = "B") /\ (pc' = "A") /\ (history' = history)

Inv == Len(history) <= 10

Liveness == <> (pc = "Done")

THEOREM Spec => []Inv
THEOREM Spec => Liveness
```