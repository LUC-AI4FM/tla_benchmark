---------------------------- MODULE Inner ----------------------------
EXTENDS Integers, Sequences

VARIABLE innerResult, innerSeq

InnerInit ==
    /\ innerResult = 0
    /\ innerSeq = <<1, 2, 3>>

InnerStep ==
    /\ innerResult = 0
    /\ innerResult' = 1
    /\ innerSeq' = SelectSeq(innerSeq, LAMBDA x: x # 1)

InnerEnabled ==
    innerResult = 0

InnerSpec ==
    InnerInit /\ [][InnerStep]_<<innerResult, innerSeq>>

=======================================================================