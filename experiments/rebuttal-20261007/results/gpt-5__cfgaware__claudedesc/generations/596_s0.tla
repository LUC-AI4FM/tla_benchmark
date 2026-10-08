----------------------------- MODULE DTConfig -----------------------------

(*
  Wrapper module that instantiates the generic DistributedTransaction
  specification with concrete keys and clients.
*)

Keys == {"k1", "k2"}

PessimisticClients == {"c1"}
OptimisticClients == {"c2"}

ReadKeys ==
  [ c \in {"c1", "c2"} |->
      IF c = "c1" THEN {} ELSE {"k1", "k2"} ]

WriteKeys ==
  [ c \in {"c1", "c2"} |->
      {"k1", "k2"} ]

PrimaryKey ==
  [ c \in {"c1", "c2"} |->
      "k1" ]

DT == INSTANCE DistributedTransaction
  WITH
    Keys <- Keys,
    PessimisticClients <- PessimisticClients,
    OptimisticClients <- OptimisticClients,
    ReadKeys <- ReadKeys,
    WriteKeys <- WriteKeys,
    PrimaryKey <- PrimaryKey

Init == DT!Init
Next == DT!Next

TypeOK == DT!TypeOK
UniqueCommitOrAbort == DT!UniqueCommitOrAbort
CommitConsistency == DT!CommitConsistency
AbortConsistency == DT!AbortConsistency
WriteConsistency == DT!WriteConsistency
UniqueWrite == DT!UniqueWrite
UniqueLockOrWrite == DT!UniqueLockOrWrite
OptimisticReadSnapshotIsolation == DT!OptimisticReadSnapshotIsolation
PessimisticReadSnapshotIsolation == DT!PessimisticReadSnapshotIsolation
MsgTsConsistency == DT!MsgTsConsistency

============================================================================