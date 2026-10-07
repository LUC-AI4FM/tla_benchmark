------------------------------ MODULE DistributedTransactionConfig ------------------------------
EXTENDS DistributedTransaction

CONSTANTS k1, k2, c1, c2

CONSTANTS
  Keys = {k1, k2},
  ClientMode = [c1 |-> "pessimistic", c2 |-> "optimistic"],
  ReadKeys = [c1 |-> {}, c2 |-> Keys],
  WriteKeys = [c1 |-> Keys, c2 |-> Keys],
  PrimaryKey = [c1 |-> k1, c2 |-> k1]

Init == DistributedTransaction.Init
Next == DistributedTransaction.Next

Spec == Init /\ [][Next]_vars /\ []TypeOK /\ []UniqueCommitOrAbort /\ []CommitConsistency /\ []AbortConsistency /\ []WriteConsistency /\ []UniqueWrite /\ []UniqueLockOrWrite /\ []OptimisticReadSnapshotIsolation /\ []PessimisticReadSnapshotIsolation /\ []MsgTsConsistency
===============================================================================