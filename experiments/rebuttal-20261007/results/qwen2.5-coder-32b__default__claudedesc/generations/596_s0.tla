------------------------------- MODULE ConfigWrapper -------------------------------
EXTENDS DistributedTransaction

CONSTANTS k1, k2, c1, c2

VARIABLES <<>>

KEYS == {k1, k2}
CLIENTS == {c1, c2}
P_CLIENTS == {c1}
O_CLIENTS == {c2}

ClientKeys == [c1 |-> KEYS, c2 |-> KEYS]
ClientPrimaryKeys == [c1 |-> k1, c2 |-> k1]
ClientReadKeys == [c1 |-> {}, c2 |-> KEYS]
ClientWriteKeys == [c1 |-> KEYS, c2 |-> KEYS]

Init == DistributedTransaction!Init
Next == DistributedTransaction!Next

Spec ==
  WF_next(<<Init, Next>>)
    /\ []TypeOK
    /\ []UniqueCommitOrAbort
    /\ []CommitConsistency
    /\ []AbortConsistency
    /\ []WriteConsistency
    /\ []UniqueWrite
    /\ []UniqueLockOrWrite
    /\ []OptimisticReadSnapshotIsolation
    /\ []PessimisticReadSnapshotIsolation
    /\ []MsgTsConsistency

=============================================================================