```
MODULE Outer
EXTENDS Integers, Sequences
CONSTANTS InnerSeq
VARIABLES result, seq

Inner(result, seq) == 
  /\ result = 0
  /\ seq = <<>>

NextInner(result, seq) == 
  /\ result' = 1
  /\ seq' = SelectSeq(LAMBDA x : x # 1, seq)

SpecInner == result = 0

Init == Inner(result, seq)
Next == 
  \/ NextInner(result, seq)
  \/ UNCHANGED <<result, seq>>
Spec == Init /\ [][Next]_<<result, seq>> 
       /\ WF_<<result, seq>>(NextInner(result, seq))
       /\ []<>~(SpecInner)

THEOREM Spec => []<> ~(SpecInner)
```