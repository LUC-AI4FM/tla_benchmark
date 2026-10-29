```tla
_read_ts >>

\* ---------------------------------------------------------------------------
\* Termination (avoid spurious deadlock once all work is done)
\* ---------------------------------------------------------------------------
Terminated ==
    /\ \A c \in CLIENT :
          \/ client_state[c] = "aborted"
          \/ (client_state[c] = "committed" /\ client_key[c].secondary = {})
    /\ \A k \in KEY : key_lock[k] = {}
    /\ UNCHANGED vars

\* ---------------------------------------------------------------------------
\* Next-state relation and specification
\* ---------------------------------------------------------------------------
Next ==
    \/ \E c \in CLIENT :
          \/ Start(c)
          \/ StartPrewrite(c)
          \/ CommitPrimary(c)
          \/ \E k \in KEY : ReadKey(c, k)
          \/ \E k \in KEY : Prewrite(c, k)
          \/ \E k \in KEY : CommitSecondary(c, k)
    \/ Resolve
    \/ Terminated

PercolatorSpec == Init /\ [][Next]_vars

Spec == PercolatorSpec

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------
TypeInvariant ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> ClientStates]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_key \in [CLIENT -> [primary : KEY,
                                  secondary : SUBSET KEY,
                                  pending : SUBSET KEY]]
    /\ client_read \in [CLIENT -> SUBSET ReadType]
    /\ key_lock \in [KEY -> SUBSET LockType]
    /\ key_write \in [KEY -> SUBSET WriteType]
    /\ key_data \in [KEY -> SUBSET Nat]
    /\ key_last_read_ts \in [KEY -> Nat]

WriteConsistency ==
    /\ \A k \in KEY : \A w \in key_write[k] :
          /\ w.type = "write" =>
                (w.start_ts < w.ts /\ w.start_ts \in key_data[k])
          /\ w.type = "rollback" => w.ts = w.start_ts
    /\ \A k1, k2 \in KEY :
          \A w1 \in key_write[k1], w2 \in key_write[k2] :
             (/\ w1.type = "write"
              /\ w2.type = "write"
              /\ w1.start_ts = w2.start_ts) => w1.ts = w2.ts

LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] :
              /\ l.ts \in key_data[k]
              /\ l.ts < l.min_commit_ts
              /\ ~\E w \in key_write[k] : w.start_ts = l.ts
              /\ \/ \E l2 \in key_lock[l.primary] : l2.ts = l.ts
                 \/ \E w \in key_write[l.primary] : w.start_ts = l.ts

CommittedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "committed" =>
            LET s   == client_ts[c].start_ts
                cts == client_ts[c].commit_ts
                rec == [ts |-> cts, start_ts |-> s, type |-> "write"]
            IN
            /\ s < cts
            /\ rec \in key_write[client_key[c].primary]
            /\ \A k \in CLIENT_KEY[c] :
                  \/ \E l \in key_lock[k] : l.ts = s
                  \/ rec \in key_write[k]
            /\ \A k \in KEY :
                  ~\E w \in key_write[k] : w.start_ts = s /\ w.type = "rollback"

AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            \A k \in KEY :
                ~\E w \in key_write[k] :
                    /\ w.start_ts = client_ts[c].start_ts
                    /\ w.type = "write"

RollbackConsistency ==
    \A k \in KEY : \A w \in key_write[k] :
        w.type = "rollback" =>
            /\ w.start_ts \notin key_data[k]
            /\ ~\E l \in key_lock[k] : l.ts = w.start_ts
            /\ \A k2 \in KEY :
                  ~\E w2 \in key_write[k2] :
                      w2.start_ts = w.start_ts /\ w2.type = "write"

UniqueWrite ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        /\ w1.start_ts = w2.start_ts => w1 = w2
        /\ (w1.type = "write" /\ w2.type = "write" /\ w1.ts = w2.ts) => w1 = w2

SnapshotIsolation ==
    \* first-committer-wins: no overlapping committed writers on a key
    /\ \A k \in KEY : \A w1, w2 \in key_write[k] :
          (/\ w1.type = "write"
           /\ w2.type = "write"
           /\ w1 # w2) =>
              (w1.ts < w2.start_ts \/ w2.ts < w1.start_ts)
    \* every snapshot read remains the latest write visible at start_ts
    /\ \A c \in CLIENT : \A r \in client_read[c] :
          r.seen = VisibleWrite(r.key, client_ts[c].start_ts)

=============================================================================
```