------------------------------- MODULE OuterModule -------------------------------
EXTENDS Integers, Sequences

CONSTANTS InnerResult, InnerSeq

VARIABLES result, seq

InnerStep == 
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x: x # result')

Init ==
    /\ result = 0
    /\ seq = << >>

Next ==
    \/ InnerStep
    \/ /\ result' = result
       /\ seq' = seq

Spec ==
    /\ Init
    /\ [][Next]_<<result, seq>>
    /\ WF_[InnerStep]_<<result, seq>>

Liveness ==
    <>[](result # 0)

=============================================================================