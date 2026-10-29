---------------------------- MODULE Outer ----------------------------
EXTENDS Naturals, Sequences

---------------------------- MODULE Inner ----------------------------
VARIABLES result, s

Step ==
    /\ result = 0
    /\ result' = 1
    /\ s' = SelectSeq(s, LAMBDA e : e # result')
=======================================================================