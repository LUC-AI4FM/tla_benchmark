```tla
 a committed write on any key.
AbortedConsistency ==
    \A c \in CLIENT : client_state[c] = "aborted" =>
        \A k \in KEY : ~IsCommitted(k, client_ts[c].start_ts)

\* If a transaction has a rollback record on any key, it is committed nowhere.
RollbackConsistency ==
    \A k \in KEY : \A i \in DOMAIN key_write[k] :
        key_write[k][i].type = "rollback" =>
            \A k2 \in KEY : ~IsCommitted(k2, key_write[k][i].start_ts)

\* On each key, committed write records have distinct start and commit
\* timestamps.
UniqueWrite ==
    \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
        LET a == key_write[k][i]
            b == key_write[k][j]
        IN
        (i # j /\ a.type = "write" /\ b.type = "write") =>
            /\ a.start_ts # b.start_ts
            /\ a.ts # b.ts

\* No write-write conflicts: for two committed writes on the same key, the
\* earlier-started transaction committed before the later one started.
SnapshotIsolation ==
    \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
        LET a == key_write[k][i]
            b == key_write[k][j]
        IN
        (a.type = "write" /\ b.type = "write" /\ a.start_ts < b.start_ts) =>
            a.ts < b.start_ts

=============================================================================
```