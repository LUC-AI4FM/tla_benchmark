------------------------------- MODULE OuterModule -------------------------------
EXTENDS Integers, Sequences

CONSTANTS InnerResult, InnerSeq

VARIABLES Result, Seq

InnerStep == 
    \/ Result = 0 /\ Seq \in Seq(UNION {0, 1})
    -> Result' = 1
       /\ Seq' = SelectSeq(Seq, LAMBDA x: x # 1)

Init ==
    /\ Result = 0
    /\ Seq = <<0>>

Next ==
    \/ InnerStep
    \/ /\ Result = 1
       /\ Seq = <<>>
       /\ UNCHANGED <<Result, Seq>>

Spec ==
    /\ Init
    /\ [][Next]_<<Result, Seq>>
    /\ WF_[InnerStep]_<<Result, Seq>>
    /\ <>[<>(Result = 1 /\ Seq = <<>>)]_<<Result, Seq>>

=============================================================================