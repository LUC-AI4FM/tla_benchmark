```
MODULE TwoStateProcess
EXTENDS Integers

CONSTANTS Done

VARIABLES pc, history

Init == (pc = "A") /\ (history = <<>>)

Next == 
  \/ (pc = "A") /\ (pc' = "B") /\ (history' = Append(history, "A")) /\ (pc = "A")
  \/ (pc = "B") /\ (pc' = "A") /\ (history' = history) /\ (pc = "B")
  \/ (pc' = pc) /\ (history' = history)

Spec == Init /\ [][Next]_<<pc, history>>
           /\ WF_<<pc, history>>((pc = "A") \/ (pc = "B"))

StateConstraint == Len(history) <= 10

Liveness == <>[](pc = "Done")

THEOREM Spec => []StateConstraint
THEOREM Spec => Liveness
```