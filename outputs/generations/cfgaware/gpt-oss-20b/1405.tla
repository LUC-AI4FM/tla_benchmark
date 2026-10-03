MODULE Inner
EXTENDS Sequences

VARIABLES result, seq

Init == /\ result = 0
      /\ seq   = <<>>

Step ==
  /\ result = 0
  /\ result' = 1
  /\ seq'    = SELECT seq WHERE \lambda x : x #= result'

Next == Step

vars == {result, seq}

SpecInner == Init /\ [][Next]_vars


MODULE Outer
EXTENDS Sequences

VARIABLES outerResult, outerSeq

InitOuter ==
  /\ outerResult = 0
  /\ outerSeq   = <<>>

INSTANCE Inner WITH
    result' = outerResult,
    seq'    = outerSeq

vars == {outerResult, outerSeq}

Stutter == \A v \in vars : v' = v

Next ==
  \/ Step
  \/ (Stutter /\ ~Step)

Spec == InitOuter /\ [][Next]_vars
SpecRunsToEnd == Spec /\ WF_vars[Step] /\ <> [] ~Step