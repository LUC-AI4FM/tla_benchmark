------------------------------ MODULE Consensus ------------------------------
EXTENDS SET, TLC

CONSTANTS Values

VARIABLES chosen

vars == <<chosen>>

Init == chosen = {}

Next ==
  /\ chosen = {}
  /\ chosen' \in { {v} : v \in Values }

Stutter == chosen' = chosen

Spec == Init /\ [] (Next \/ Stutter)

TypeOK == chosen \in SUBSET Values

ConsistencyInv ==
  chosen = {} \/ (\E v \in Values : chosen = {v})

LiveSpec == Spec /\ WF/Next

Success == <> (chosen != {})

THEOREM Spec_implies_TypeOK == Spec => [] TypeOK
THEOREM Spec_implies_ConsistencyInv == Spec => [] ConsistencyInv
THEOREM LiveSpec_implies_Success == LiveSpec => <> Success

=============================================================================