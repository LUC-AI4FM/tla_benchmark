---------------------------- MODULE SelectSeqPrimeInstance ----------------------------
EXTENDS Sequences, Naturals

---------------------------- MODULE Inner725f ----------------------------
EXTENDS Sequences, Naturals

VARIABLES res, myseq

Step ==
    /\ res = 0
    /\ res' = 1
    /\ myseq' = SelectSeq(myseq, LAMBDA x : x # res')

Fairness == WF_<<res, myseq>>(Step)
==========================================================================