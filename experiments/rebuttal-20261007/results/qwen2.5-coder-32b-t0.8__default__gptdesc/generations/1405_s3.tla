```tla
MODULE OuterModule

EXTENDS TLC, Sequences, FiniteSets

CONSTANTS InnerResult, InnerSequence

VARIABLES result, sequence

InnerStep == 
  /\ result = 0
  /\ result' = 1
  /\ sequence' = SelectSeq(sequence, LAMBDA x: x # 1)

Init ==
  /\ result = 0
  /\ sequence = <<>>

Next ==
  \/ InnerStep
  \/ \/ stuttering
     <\/ result' = result
        /\ sequence' = sequence

Spec == 
  Init /\ [][Next]_<<result, sequence>> /\ WF_<<result, sequence>>(InnerStep)

THEOREM Spec => <>[]~(result = 0)
```