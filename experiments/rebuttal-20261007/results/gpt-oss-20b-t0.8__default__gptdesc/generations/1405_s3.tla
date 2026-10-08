```
MODULE Outer
EXTENDS Sequences

VARIABLES r, seq

SeqFilter(seq, pred) == 
  Subseq(seq,
         { i \in 1..Len(seq) : pred(seq[i]) })

Init ==
  /\ r = 0
  /\ seq = <<>>

InnerStep ==
  /\ r = 0
  /\ r' = 1
  /\ seq' = SeqFilter(seq, \lambda x : x #= 1)

Stutter ==
  /\ r' = r
  /\ seq' = seq

Next == 
  IF r = 0 THEN
      \/ InnerStep
      \/ Stutter
    ELSE
      Stutter

Spec ==
  Init
  /\ [][Next]_<<r, seq>>
  /\ WF_ <<r, seq>> (InnerStep)
  /\ <> [] (~Enabled(InnerStep))
```