```tla
MODULE OuterModule
EXTENDS Integers, Sequences

CONSTANTS InnerSeq

VARIABLES innerResult, innerSequence

Init == (innerResult = 0) /\ (innerSequence = <<>>)

InnerStep == (innerResult' = 1) /\ (innerSequence' = SelectSeq(LAMBDA x : x # innerResult', innerSequence))

Next == IF (innerResult = 0)
           THEN InnerStep
           ELSE (innerResult' = innerResult) /\ (innerSequence' = innerSequence)

Spec == Init /\ [][Next]_<<innerResult, innerSequence>>
       /\ WF_<<innerResult, innerSequence>>(InnerStep)

THEOREM Spec => <>[]~(InnerStep)
```