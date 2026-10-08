------------------------------- MODULE OuterModule ------------------------------
EXTENDS TLC, Sequences

CONSTANTS InnerResult, InnerSeq

VARIABLES result, seq

InnerStep == 
    \/ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x: x # result')

Init ==
    \/ result = 0
    /\ seq = <<>>

Next ==
    \/ InnerStep
    \/ \<\> -- stuttering

Spec ==
    INIT Init
    NEXT Next
    WF_next(InnerStep)
    SF_next(InnerStep)

Invariant ==
    /\ (result = 0 \/ result = 1)
    /\ seq \in Seq(Nat)

Liveness ==
    <>[](<>[]~InnerStep)

===============================================================================