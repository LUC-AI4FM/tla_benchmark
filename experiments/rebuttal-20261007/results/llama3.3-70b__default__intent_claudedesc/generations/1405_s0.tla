```
MODULE Inner
EXTENDS Integers
CONSTANTS Result, Seq
VARIABLES result, seq

Init == (result = 0) /\ (seq = Seq)

Next == IF result = 1 THEN
           (result' = result) /\ (seq' = SelectSeq(seq, lambda x : x # 1))
         ELSE
           (result' = 1) /\ (seq' = SelectSeq(seq, lambda x : x # 1))

Spec == Init /\ [][Next]_<<result, seq>>
THEOREM Spec => []<>~Enabled(<Next>_)
======================================

MODULE Outer
EXTENDS Inner
VARIABLES result, seq

Init == (result = 0) /\ (seq = <<1, 2, 3>>)

Next == IF Enabled(Inner!Next)
           THEN Inner!Next
           ELSE (result' = result) /\ (seq' = seq)

Spec == Init /\ [][Next]_<<result, seq>>
Fairness == WF_<<result, seq>>(Inner!Next)
THEOREM Spec /\ Fairness => []<>~Enabled(Inner!Next)
```