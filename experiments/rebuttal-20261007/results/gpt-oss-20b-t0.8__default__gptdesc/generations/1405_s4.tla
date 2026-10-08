```tla
---- MODULE Inner ----
EXTENDS Sequences

VARIABLES result, seq

Init == /\ result = 0
        /\ seq = <<>>

Step ==
    /\ result = 0
    /\ result' = 1
    /\ seq' =
          Subseq(seq,
                 {i \in 1..Len(seq) : seq[i] # 1})

Next == Step

Spec == Init /\ [][Next]_<<result, seq>>
```


```tla
---- MODULE Outer ----
EXTENDS Sequences

INSTANCE Inner AS X WITH
    result -> xResult,
    seq -> xSeq

VARIABLES xResult, xSeq

Init ==
    /\ xResult = 0
    /\ xSeq = <<>>

Stutter == UNCHANGED <<xResult, xSeq>>

Next == \/ X.Step
          \/ Stutter

Spec ==
    Init
    /\ [][Next]_<<xResult, xSeq>>
    /\ WF_{xResult,xSeq}(X.Step)
    /\ <>[]~Enabled(X.Step)
```