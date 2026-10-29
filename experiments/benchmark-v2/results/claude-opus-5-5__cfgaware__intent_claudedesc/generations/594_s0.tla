```tla
ite ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] : ~\E w \in key_write[k] : w.start_ts = l.ts

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    w1.commit_ts = w2.commit_ts => w1 = w2

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : \A k \in CLIENT_READ_KEY[c] :
    client_read[c][k] # -1 => client_read[c][k] = LatestWrite(k, StartTs(c))

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : client_state[c] = "committed" =>
    \A k \in CLIENT_READ_KEY[c] :
      client_read[c][k] = LatestWrite(k, CommitTs(c) - 1)

MsgTsConsistency ==
  /\ \A c \in CLIENT : client_state[c] # "init" =>
       /\ StartTs(c) > 0
       /\ StartTs(c) < next_ts
       /\ c \in PESSIMISTIC_CLIENT =>
            (StartTs(c) <= ForUpdateTs(c) /\ ForUpdateTs(c) < next_ts)
       /\ client_state[c] = "committed" =>
            /\ CommitTs(c) > StartTs(c)
            /\ CommitTs(c) > ForUpdateTs(c)
            /\ CommitTs(c) < next_ts
  /\ \A k \in KEY : \A l \in key_lock[k] :
       /\ l.ts < next_ts
       /\ l.for_update_ts < next_ts
  /\ \A k \in KEY : \A w \in key_write[k] : w.commit_ts < next_ts

=============================================================================
```