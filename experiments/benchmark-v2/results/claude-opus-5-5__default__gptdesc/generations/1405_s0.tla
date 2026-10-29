---------------------------- MODULE OuterSelectSeqLambda ----------------------------
EXTENDS Naturals, Sequences

---------------------------- MODULE Inner ----------------------------
EXTENDS Naturals, Sequences

VARIABLES result, sq

\* Single action: result goes from 0 to 1, and every element equal
\* to the new result value is filtered out of the sequence.
Step ==
    /\ result = 0
    /\ result' = 1
    /\ sq' = SelectSeq(sq, LAMBDA e : e # result')
=============================================================================