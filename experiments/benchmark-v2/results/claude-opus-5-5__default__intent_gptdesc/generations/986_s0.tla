```tla
LED Next) <=> Terminated

(******************************* Liveness *********************************)
EventuallyTerminates == <>Terminated

StaysTerminated == <>[]Terminated

EventuallyLeader == <>(\E n \in Nodes : IsLeader(n))

(******************************* Theorems *********************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []NeighborInv
THEOREM Spec => []EdgeConsistency
THEOREM Spec => []MessageInv
THEOREM Spec => []KindInv
THEOREM Spec => []MailboxUnique
THEOREM Spec => []AtMostOneLeader
THEOREM Spec => []LeaderIsMin
THEOREM Spec => []MinNeverPruned
THEOREM Spec => []LeaderImpliesTermination
THEOREM Spec => []DeadlockIffTermination
THEOREM Spec => EventuallyTerminates
THEOREM Spec => StaysTerminated
=============================================================================
```