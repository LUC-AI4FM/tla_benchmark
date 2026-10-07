------------------------------ MODULE DT_Config ------------------------------

EXTENDS Naturals

CONSTANTS k1, k2, c1, c2

INSTANCE DistributedTransaction
  WITH
    Keys <- {k1, k2},
    PessimisticClients <- {c1},
    OptimisticClients <- {c2},
    ReadSet <- [ c \in {c1, c2} |-> IF c = c1 THEN {} ELSE {k1, k2} ],
    WriteSet <- [ c \in {c1, c2} |-> {k1, k2} ],
    PrimaryKey <- [ c \in {c1, c2} |-> k1 ]

VARIABLES dummy

Init == DistributedTransaction!Init
Next == DistributedTransaction!Next

Spec == DistributedTransaction!Spec

TypeOK == DistributedTransaction!TypeOK
UniqueCommitOrAbort == DistributedTransaction!UniqueCommitOrAbort
CommitConsistency == DistributedTransaction!CommitConsistency
AbortConsistency == DistributedTransaction!AbortConsistency
WriteConsistency == DistributedTransaction!WriteConsistency
UniqueWrite == DistributedTransaction!UniqueWrite
UniqueLockOrWrite == DistributedTransaction!UniqueLockOrWrite
OptimisticReadSnapshotIsolation == DistributedTransaction!OptimisticReadSnapshotIsolation
PessimisticReadSnapshotIsolation == DistributedTransaction!PessimisticReadSnapshotIsolation
MsgTsConsistency == DistributedTransaction!MsgTsConsistency

=============================================================================