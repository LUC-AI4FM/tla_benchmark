------------------------------ MODULE OuterSpec ------------------------------
EXTENDS Naturals, Sequences

------------------------------ MODULE Inner ------------------------------
EXTENDS Naturals, Sequences

VARIABLES result, seq

Step ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x : x # result')
==========================================================================