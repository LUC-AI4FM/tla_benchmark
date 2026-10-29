------------------------------- MODULE SelectSeqInstance -------------------------------
EXTENDS Naturals, Sequences

---------------------------------- MODULE Inner ----------------------------------
EXTENDS Naturals, Sequences

VARIABLES s, res

Step ==
    /\ res = 0
    /\ res' = 1
    /\ s' = SelectSeq(s, LAMBDA x : x # res')
==================================================================================