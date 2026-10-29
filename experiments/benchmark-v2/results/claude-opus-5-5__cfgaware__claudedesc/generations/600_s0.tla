```tla
               w.start_ts = r.start_ts /\ w.type = "write"

UniqueWrite ==
  \A k \in KEY :
    \A w1, w2 \in key_write[k] :
      w1 # w2 => (w1.ts # w2.ts /\ w1.start_ts # w2.start_ts)

SnapshotIsolation ==
  /\ \A k \in KEY :
       \A w1, w2 \in key_write[k] :
         (/\ w1 # w2
          /\ w1.type = "write"
          /\ w2.type = "write") =>
            \/ w1.ts < w2.start_ts
            \/ w2.ts < w1.start_ts
  /\ \A k \in KEY :
       \A l \in key_lock[k] : l.min_commit_ts > key_last_read_ts[k]

=============================================================================
```