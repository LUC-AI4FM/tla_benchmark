```
MODULE Outer
EXTENDS Integers, Sequences
CONSTANTS InnerSeq
VARIABLES innerResult, innerSequence

Inner == INSTANCE InnerModule WITH result <- innerResult, sequence <- innerSequence

Init ==
  /\ innerResult = 0
  /\ innerSequence = <<1, 2, 3>>

Next ==
  \/ Inner!Step
  \/ UNCHANGED <<innerResult, innerSequence>>

Spec == Init /\ [][Next]_<<innerResult, innerSequence>>
          /\ WF_<<innerResult, innerSequence>>(Inner!Step)

THEOREM Spec => <>[](~Enabled(Inner!Step))
============================================================

MODULE InnerModule
EXTENDS Integers, Sequences
CONSTANTS Seq
VARIABLES result, sequence

Step ==
  /\ result' = 1
  /\ sequence' = SelectSeq(LAMBDA x : x # sequence : x /= result', sequence)
  /\ UNCHANGED << >>

Enabled(Step) == result = 0
```