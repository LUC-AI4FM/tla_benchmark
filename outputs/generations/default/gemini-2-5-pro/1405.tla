---------------------------- MODULE OuterModule ----------------------------
EXTENDS Integers, Sequences

InnerModule ==
    MODULE
        EXTENDS Sequences
        VARIABLES result, seq
        InnerStep ==
            /\ result = 0
            /\ result' = 1
            /\ seq' = SelectSeq(seq, LAMBDA v: v /= 1)
    END

CONSTANT InitialSeq
VARIABLES outer_result, outer_seq

I == INSTANCE InnerModule WITH result <- outer_result, seq <- outer_seq

Init ==
    /\ outer_result = 0
    /\ outer_seq = InitialSeq

OuterStep == I!InnerStep

Next ==
    \/ OuterStep
    \/ UNCHANGED <<outer_result, outer_seq>>

Spec == Init /\ [][Next]_<<outer_result, outer_seq>>

Fairness == WF_<<outer_result, outer_seq>>(OuterStep)

LivenessProperty == <>([]~ENABLED OuterStep)

THEOREM Spec /\ Fairness => LivenessProperty

=============================================================================