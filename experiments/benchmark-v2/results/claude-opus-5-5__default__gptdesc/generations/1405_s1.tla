---------------------------- MODULE OuterSpec ----------------------------
EXTENDS Naturals, Sequences

---------------------------- MODULE InnerSpec ----------------------------
EXTENDS Naturals, Sequences

VARIABLES result, seq

Step ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x : x # result')
==========================================================================