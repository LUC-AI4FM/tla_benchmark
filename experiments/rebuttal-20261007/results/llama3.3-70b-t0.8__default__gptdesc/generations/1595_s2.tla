```
MODULE Counter
EXTENDS Integers

CONSTANTS

VARIABLES pc, x

Init == (pc = "Start") /\ (x = 0)

Next == IF pc = "Start" THEN (pc' = "Loop") /\ (x' = 0)
        ELSE IF pc = "Loop" THEN
                 IF x < 10 THEN (pc' = "Loop") /\ (x' = x + 1)
                 ELSE (pc' = "Done") /\ (x' = x)
        ELSE (pc' = pc) /\ (x' = x)

Spec == Init /\ [][Next]_<<pc, x>>
         /\ WF_<<pc, x>>(Next)

AtFive == (x = 5)

FinishLoop == (pc = "Loop") /\ (x = 10)

PossibleCounts == 
  LET CountStates == { "Start", "Loop", "Done" }
  IN \A s \in CountStates : ~ENABLED <<Next>>_<<pc, x>> @ s

THEOREM Spec => <>[]pc = "Done"
```