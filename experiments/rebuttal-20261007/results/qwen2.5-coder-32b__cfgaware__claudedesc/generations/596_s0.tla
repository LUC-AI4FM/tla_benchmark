------------------------------- MODULE DistributedTransactionConfig -------------------------------

CONSTANTS
    k1, k2,
    c1, c2

VARIABLES
    state

ASSUME TYPEOK == <<k1, k2>> \in Seq(KEYS) /\ <<c1, c2>> \in Seq(CLIENTS)

KEYS == {k1, k2}
CLIENTS == {c1, c2}

PRIMARY_KEY == [c1 |-> k1, c2 |-> k1]
READ_KEYS == [c1 |-> {}, c2 |-> KEYS]
WRITE_KEYS == [c1 |-> KEYS, c2 |-> KEYS]

MODE_CLASSIFICATION == [c1 |-> "pessimistic", c2 |-> "optimistic"]

INSTANCE DistributedTransaction WITH
    KEYS <- KEYS,
    CLIENTS <- CLIENTS,
    PRIMARY_KEY <- PRIMARY_KEY,
    READ_KEYS <- READ_KEYS,
    WRITE_KEYS <- WRITE_KEYS,
    MODE_CLASSIFICATION <- MODE_CLASSIFICATION

Init == DistributedTransaction!Init
Next == DistributedTransaction!Next

Spec == Init /\ [][Next]_<<state>>

TYPEOK == DistributedTransaction!TypeOK
UniqueCommitOrAbort == DistributedTransaction!UniqueCommitOrAbort
CommitConsistency == DistributedTransaction!CommitConsistency
AbortConsistency == DistributedTransaction!AbortConsistency
WriteConsistency == DistributedTransaction!WriteConsistency
UniqueWrite == DistributedTransaction!UniqueWrite
UniqueLockOrWrite == DistributedTransaction!UniqueLockOrWrite
OptimisticReadSnapshotIsolation == DistributedTransaction!OptimisticReadSnapshotIsolation
PessimisticReadSnapshotIsolation == DistributedTransaction!PessimisticReadSnapshotIsolation
MsgTsConsistency == DistributedTransaction!MsgTsConsistency

=================================================================================================