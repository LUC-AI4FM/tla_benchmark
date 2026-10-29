---------------------------- MODULE OuterSelectSeq ----------------------------
EXTENDS Naturals, Sequences

    ---------------------------- MODULE InnerSelectSeq ----------------------------
    VARIABLES result, seq

    Step == /\ result = 0
            /\ result' = 1
            /\ seq' = SelectSeq(seq, LAMBDA x : x # result')
    ================================================================================