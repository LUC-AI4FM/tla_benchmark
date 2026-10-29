---- MODULE SelectSeqInstance ----
EXTENDS Naturals, Sequences

---- MODULE Inner ----
VARIABLES result, seq

Step ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA e : e # result')
====