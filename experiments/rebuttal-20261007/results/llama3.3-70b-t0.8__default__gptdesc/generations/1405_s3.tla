```
MODULE Outer
EXTENDS Integers, Sequences
CONSTANTS InnerResultInit, SeqInit
VARIABLES inner_result, seq

Inner == INSTANCE InnerModule WITH result <- inner_result, sequence <- seq

Init ==
  /\ inner_result = InnerResultInit
  /\ seq = SeqInit

Next ==
  /\ (inner_result # 1 -> INNER_Next)
  /\ (INNER_Disabled -> UNCHANGED <<inner_result, seq>>)

Spec == Init /\ [][Next]_<<inner_result, seq>>
           /\ WF_<<inner_result, seq>>(INNER_Next)

THEOREM Spec => <>[]INNER_Disabled
============================================================================

MODULE InnerModule
EXTENDS Integers, Sequences
CONSTANTS resultInit, sequenceInit
VARIABLES result, sequence

Inner_Next ==
  /\ result' = 1
  /\ sequence' = SelectSeq(LAMBDA x : x # result', sequence)

INNER_Disabled == result = 1

============================================================================
```