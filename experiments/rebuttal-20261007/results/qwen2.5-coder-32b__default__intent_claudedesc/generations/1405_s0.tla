------------------------------- MODULE InnerModule -------------------------------
VARIABLES result, seq

CONSTANTS InitResult, InitSeq

Init == /\ result = InitResult
        /\ seq = InitSeq

Next == \/ /\ result = 0
            /\ result' = 1
            /\ seq' = SelectSeq(seq, \e -> e # 1)
        \/ /\ result' = result
           /\ seq' = seq

Spec == Init /\ [][Next]_<<result, seq>>

=============================================================================