---- MODULE Inner725f ----
EXTENDS Sequences, Integers

VARIABLES res, myseq

vars == <<res, myseq>>

Init ==
  /\ res = 0
  /\ myseq = <<1, 2, 3>>

Step ==
  /\ res = 0
  /\ res' = 1
  /\ myseq' = SelectSeq(myseq, LAMBDA e: e /= res')

Fairness == WF_vars(Step)
====