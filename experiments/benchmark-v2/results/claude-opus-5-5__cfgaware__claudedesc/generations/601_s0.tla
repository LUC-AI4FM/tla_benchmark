------------------

TypeInvariant ==
    /\ next_ts \in Nat
    /\ \A c \in CLIENT :
         /\ client_state[c] \in ClientStates
         /\ client_ts[c].start_ts \in Nat
         /\ client_ts[c].commit_ts \in Nat
         /\ client_pending[c] \subseteq KEY
         /\ \A k \in KEY : client_read[c][k] \in Nat \cup {NoRead}
    /\ \A k \in KEY :
         /\ \A l \in key_lock[k] :
              /\ l.ts \in Nat
              /\ l.primary \in KEY
              /\ l.min_commit_ts \in Nat
         /\ \A w \in key_write[k] :
              /\ w.ts \in Nat
              /\ w.start_ts \in Nat
              /\ w.type \in {"write", "rollback"}
         /\ key_data[k] \subseteq Nat
         /\ key_max_ts[k] \in Nat

\* Every committed write record points to existing data.
WriteConsistency ==
    \A k \in KEY : \A w \in key_write[k] :
        w.type = "write" => w.start_ts \in key_data[k]

\* At most one lock per key, and each lock has its data.
LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] : l.ts \in key_data[k]

\* A committed client has its primary committed, and each key is
\* either still locked (to be rolled forward) or committed; never rolled back.
CommittedConsistency ==
    \A c \in CLIENT :
        LET start == client_ts[c].start_ts
            cts == client_ts[c].commit_ts
            rec == [ts |-> cts, start_ts |-> start, type |-> "write"]
        IN
        client_state[c] = "committed" =>
            /\ rec \in key_write[Primary(c)]
            /\ \A k \in KEY :
                 /\ \/ \E l \in key_lock[k] : l.ts = start
                    \/ rec \in key_write[k]
                 /\ ~\E w \in key_write[k] :
                        w.start_ts = start /\ w.type = "rollback"

\* An aborted client never has a committed primary.
AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            ~\E w \in key_write[Primary(c)] :
                w.start_ts = client_ts[c].start_ts /\ w.type = "write"

\* A transaction rolled back on a key is never committed on that key.
RollbackConsistency ==
    \A k \in KEY : \A r \in key_write[k] :
        r.type = "rollback" =>
            ~\E w \in key_write[k] :
                w.type = "write" /\ w.start_ts = r.start_ts

\* No two records on a key share a timestamp.
UniqueWrite ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        w1.ts = w2.ts => w1 = w2

\* Reads see the latest commit not after start_ts, and committed
\* transactions writing the same keys never overlap.
SnapshotIsolation ==
    /\ \A c \in CLIENT : \A k \in KEY :
         client_read[c][k] # NoRead =>
            client_read[c][k] =
              Max({client_ts[d].commit_ts :
                     d \in {e \in CLIENT :
                              /\ client_state[e] = "committed"
                              /\ client_ts[e].commit_ts <= client_ts[c].start_ts}}
                  \cup {0})
    /\ \A c, d \in CLIENT :
         (c # d /\ client_state[c] = "committed"
                /\ client_state[d] = "committed") =>
            \/ client_ts[c].commit_ts < client_ts[d].start_ts
            \/ client_ts[d].commit_ts < client_ts[c].start_ts

=============================================================================