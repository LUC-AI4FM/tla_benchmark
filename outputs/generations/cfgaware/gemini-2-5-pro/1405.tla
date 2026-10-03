----------------------------- MODULE Outer -----------------------------
EXTENDS Naturals, Sequences

-----------------------------------------------------------------------------
LOCAL MODULE Inner
VARIABLES result, seq

InnerStep == /\ result = 0
             /\ result' = 1
             /\ seq' = SelectSeq(seq, LAMBDA x: x # 1)

END MODULE
-----------------------------------------------------------------------------

VARIABLES outer_result, outer_seq

INSTANCE Inner WITH result <- outer_result, seq <- outer_seq

Init == /\ outer_result = 0
        /\ outer_seq = <<0, 1, 0, 1, 0>>

Next == InnerStep \/ UNCHANGED <<outer_result, outer_seq>>

Spec == Init /\ [][Next]_<<outer_result, outer_seq>> /\ WF_<<outer_result, outer_seq>>(InnerStep)

SpecRunsToEnd == <>[](~ENABLED InnerStep)

=============================================================================