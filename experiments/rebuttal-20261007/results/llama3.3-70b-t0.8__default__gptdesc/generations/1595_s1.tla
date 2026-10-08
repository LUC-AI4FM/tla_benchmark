```
MODULE Counter
EXTENDS Integers

CONSTANTS 
VARIABLES pc, x

Init == (pc = "Start") /\
        (x = 0)

Next == IF pc = "Start" THEN
            /\ pc' = "Loop"
            /\ x' = 0
        ELSE IF pc = "Loop" THEN
            /\ x < 10
            /\ pc' = "Loop"
            /\ x' = x + 1
        ELSE IF pc = "Loop" THEN
            /\ x = 10
            /\ pc' = "Done"
            /\ x' = x
        ELSE 
            /\ pc' = pc
            /\ x' = x

Spec == Init /\ [][Next]_<<pc, x>>
Termination == <>[]pc = "Done"

AtFive == (x = 5)
FinishLoop == (x = 10)

THEOREM Spec => []Termination

PossibleCounts == 
  YaoWeb_tlc.GetNamedStateCnts["Start"] + 
  YaoWeb_tlc.GetNamedStateCnts["Loop"] + 
  YaoWeb_tlc.GetNamedStateCnts["Done"] = 11
```