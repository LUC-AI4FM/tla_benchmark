------------------------------ MODULE Consensus ------------------------------
CONSTANTS Values

VARIABLE chosen

vars == {chosen}

Init == chosen = {}

Next == (chosen = {}) /\ (∃ v ∈ Values : chosen' = {v})

Spec == Init /\ [][Next]_vars

TypeOK == chosen \subseteq Values /\ Finite(chosen)

ConsistencyInv == #chosen <= 1

Success == <> (chosen != {})

LiveSpec == Spec /\ WF_vars(Next)

THEOREM Spec_TypeOK_Inv == Spec => [] TypeOK
THEOREM Spec_ConsistencyInv == Spec => [] ConsistencyInv
THEOREM LiveSpec_Success == LiveSpec => <> Success

------------------------------ END MODULE Consensus ------------------------------
