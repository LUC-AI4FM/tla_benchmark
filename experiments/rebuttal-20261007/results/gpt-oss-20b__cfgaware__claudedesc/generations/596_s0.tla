------------------------------ MODULE ConfigDistributedTransaction ------------------------------
EXTENDS DistributedTransaction

CONSTANTS
  Keys = {"k1", "k2"},
  Clients = {"c1", "c2"},
  PessimisticClients = {"c1"},
  OptimisticClients = {"c2"},
  ReadKeys =
    [ c \in Clients |-> IF c = "c1" THEN {} ELSE {"k1", "k2"} ],
  WriteKeys =
    [ c \in Clients |-> {"k1", "k2"} ],
  PrimaryKey =
    [ c \in Clients |-> "k1" ]

(* The following operators are provided by DistributedTransaction and
   will be used directly in the configuration:
     Init, Next,
     TypeOK,
     UniqueCommitOrAbort, CommitConsistency, AbortConsistency,
     WriteConsistency, UniqueWrite, UniqueLockOrWrite,
     OptimisticReadSnapshotIsolation, PessimisticReadSnapshotIsolation,
     MsgTsConsistency
*)

=============================================================================