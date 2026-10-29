---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Model-checking configuration wrapper for the DistributedTransaction     *)
(* specification. It instantiates the generic protocol with two concrete   *)
(* keys (k1, k2) and two clients (c1, c2):                                 *)
(*   - c1 is a pessimistic client that reads nothing and writes k1 and k2, *)
(*     with k1 as its primary key.                                         *)
(*   - c2 is an optimistic client that reads and writes k1 and k2, with k1 *)
(*     as its primary key.                                                 *)
(*                                                                         *)
(* The parent module DistributedTransaction declares these CONSTANTS:      *)
(*   KEY, OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT,                           *)
(*   CLIENT_READ_KEY, CLIENT_WRITE_KEY, CLIENT_PRIMARY                     *)
(* They are bound to the MC_* definitions below in the .cfg file.          *)
(***************************************************************************)
EXTENDS DistributedTransaction, TLC

\* Model values that stand for the concrete keys and clients.
CONSTANTS k1, k2
CONSTANTS c1, c2

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete values for the parent module's constant parameters.            *)
(***************************************************************************)

\* The set of keys.
MC_KEY == {k1, k2}

\* Clients classified by concurrency-control mode.
MC_OPTIMISTIC_CLIENT  == {c2}
MC_PESSIMISTIC_CLIENT == {c1}

\* The keys each client reads.
\* c1 reads nothing; c2 reads both keys.
MC_CLIENT_READ_KEY == [c \in {c1, c2} |->
                         IF c = c1 THEN {} ELSE {k1, k2}]

\* The keys each client writes.
\* Both clients write both keys.
MC_CLIENT_WRITE_KEY == [c \in {c1, c2} |-> {k1, k2}]

\* The primary key of each client.
\* Both clients use k1 as their primary.
MC_CLIENT_PRIMARY == [c \in {c1, c2} |-> k1]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking entry points. These are the parent's Init, Next, and     *)
(* Spec. They are re-exported under MC_* names so the configuration can    *)
(* refer to them unambiguously.                                            *)
(***************************************************************************)
MC_Init == Init
MC_Next == Next
MC_Spec == Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The ten safety invariants checked by the model checker. Each one is     *)
(* defined in the parent DistributedTransaction module.                    *)
(***************************************************************************)
MC_Invariants ==
    /\ TypeOK
    \* Atomicity and consistency of commit/abort outcomes
    /\ UniqueCommitOrAbort
    /\ CommitConsistency
    /\ AbortConsistency
    \* Correctness of write operations and lock discipline
    /\ WriteConsistency
    /\ UniqueWrite
    /\ UniqueLockOrWrite
    \* Snapshot isolation guarantees for each client class
    /\ OptimisticReadSnapshotIsolation
    /\ PessimisticReadSnapshotIsolation
    \* Timestamp consistency of messages
    /\ MsgTsConsistency

(***************************************************************************)
(* Corresponding MC_DistributedTransaction.cfg:                            *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*     k1 = k1                                                             *)
(*     k2 = k2                                                             *)
(*     c1 = c1                                                             *)
(*     c2 = c2                                                             *)
(*     KEY                <- MC_KEY                                        *)
(*     OPTIMISTIC_CLIENT  <- MC_OPTIMISTIC_CLIENT                          *)
(*     PESSIMISTIC_CLIENT <- MC_PESSIMISTIC_CLIENT                         *)
(*     CLIENT_READ_KEY    <- MC_CLIENT_READ_KEY                            *)
(*     CLIENT_WRITE_KEY   <- MC_CLIENT_WRITE_KEY                           *)
(*     CLIENT_PRIMARY     <- MC_CLIENT_PRIMARY                             *)
(*   INIT Init                                                             *)
(*   NEXT Next                                                             *)
(*   INVARIANTS                                                            *)
(*     TypeOK                                                              *)
(*     UniqueCommitOrAbort                                                 *)
(*     CommitConsistency                                                   *)
(*     AbortConsistency                                                    *)
(*     WriteConsistency                                                    *)
(*     UniqueWrite                                                         *)
(*     UniqueLockOrWrite                                                   *)
(*     OptimisticReadSnapshotIsolation                                     *)
(*     PessimisticReadSnapshotIsolation                                    *)
(*     MsgTsConsistency                                                    *)
(***************************************************************************)
=============================================================================