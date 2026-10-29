asCommittedWrite(k, client_ts[c].start_ts)
              /\ \E k \in KEY : HasRollback(k, client_ts[c].start_ts)

\* Uniqueness: each start ts appears at most once among a key's records.
UniqueWrite ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        w1.start_ts = w2.start_ts => w1 = w2

\* Snapshot isolation: no committed write ever lands at commit_ts <= a
\* timestamp at which the key was already read.
SnapshotIsolation ==
    \A k \in KEY : key_si[k]

Invariants ==
    /\ TypeOK
    /\ WellFormed
    /\ WriteConsistency
    /\ LockConsistency
    /\ CommittedConsistency
    /\ AbortConsistency
    /\ RollbackConsistency
    /\ UniqueWrite
    /\ SnapshotIsolation

-----------------------------------------------------------------------------
\* Liveness properties

\* Once committed, every secondary lock of the transaction is eventually resolved.
SecondaryEventuallyResolved ==
    \A c \in CLIENT :
        (client_state[c] = "committed") ~>
            (\A k \in client_key[c].secondary :
                ~HasLockEQ(k, client_ts[c].start_ts))

\* A transaction past its commit-ts assignment eventually commits or aborts.
CommittingEventuallyFinishes ==
    \A c \in CLIENT :
        (client_state[c] = "committing") ~>
            (client_state[c] \in {"committed", "aborted"})

THEOREM Spec => []Invariants
THEOREM Spec => SecondaryEventuallyResolved /\ CommittingEventuallyFinishes
=============================================================================
```