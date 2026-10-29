```tla
s \cup {[c |-> c, type |-> "prewrite",
                                     start_ts |-> sts, commit_ts |-> 0]}
            /\ UNCHANGED <<next_ts, client_state, client_ts, client_locked,
                           key_write, reads>>

PessLock(c, k) ==
  LET sts == client_ts[c].start_ts
      fts == client_ts[c].for_update_ts
  IN
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ k \in CLIENT_WRITE_KEY[c] \ client_locked[c]
  /\ key_lock[k] = {}
  /\ IF \E w \in key_write[k] : w.start_ts = sts
       THEN AbortClient(c)
       ELSE IF \E w \in Writes(k) : w.ts > fts
         THEN /\ next_ts' = next_ts + 1
              /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts + 1]
              /\ UNCHANGED <<client_state, client_locked, client_prewritten,
                             key_lock, key_write, key_data, reads, msgs>>
         ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                   {[ts |-> sts, primary |-> CLIENT_PRIMARY[c],
                     type |-> "lock_key", for_update_ts |-> fts]}]
              /\ client_locked' = [client_locked EXCEPT ![c] = @ \cup {k}]
              /\ UNCHANGED <<next_ts, client_state, client_ts,
                             client_prewritten, key_write, key_data,
                             reads, msgs>>

PessPrewrite(c, k) ==
  LET sts == client_ts[c].start_ts IN
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ client_locked[c] = CLIENT_WRITE_KEY[c]
  /\ k \in CLIENT_WRITE_KEY[c] \ client_prewritten[c]
  /\ IF \E l \in key_lock[k] : l.ts = sts
       THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                 {[l EXCEPT !.type = "prewrite_pessimistic"] : l \in key_lock[k]}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {sts}]
            /\ client_prewritten' = [client_prewritten EXCEPT ![c] = @ \cup {k}]
            /\ msgs' = msgs \cup {[c |-> c, type |-> "prewrite",
                                   start_ts |-> sts, commit_ts |-> 0]}
            /\ UNCHANGED <<next_ts, client_state, client_ts, client_locked,
                           key_write, reads>>
       ELSE AbortClient(c)

GetCommitTs(c) ==
  /\ client_state[c] = "working"
  /\ client_prewritten[c] = CLIENT_WRITE_KEY[c]
  /\ ReadKeysOf(c) = CLIENT_READ_KEY[c]
  /\ next_ts' = next_ts + 1
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts + 1]
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ msgs' = msgs \cup {[c |-> c, type |-> "commit",
                         start_ts |-> client_ts[c].start_ts,
                         commit_ts |-> next_ts + 1]}
  /\ UNCHANGED <<client_locked, client_prewritten, key_lock, key_write,
                 key_data, reads>>

CommitPrimary(c) ==
  LET p   == CLIENT_PRIMARY[c]
      sts == client_ts[c].start_ts
      cts == client_ts[c].commit_ts
  IN
  /\ client_state[c] = "committing"
  /\ IF \E l \in key_lock[p] : l.ts = sts
       THEN /\ key_lock' = [key_lock EXCEPT ![p] = {}]
            /\ key_write' = [key_write EXCEPT ![p] =
                  @ \cup {[ts |-> cts, start_ts |-> sts, type |-> "write"]}]
            /\ client_state' = [client_state EXCEPT ![c] = "committed"]
            /\ UNCHANGED <<next_ts, client_ts, client_locked,
                           client_prewritten, key_data, reads, msgs>>
       ELSE AbortClient(c)

CommitSecondary(c, k) ==
  LET sts == client_ts[c].start_ts
      cts == client_ts[c].commit_ts
  IN
  /\ client_state[c] = "committed"
  /\ k \in CLIENT_WRITE_KEY[c]
  /\ k # CLIENT_PRIMARY[c]
  /\ \E l \in key_lock[k] : l.ts = sts
  /\ key_lock' = [key_lock EXCEPT ![k] = {}]
  /\ key_write' = [key_write EXCEPT ![k] =
        @ \cup {[ts |-> cts, start_ts |-> sts, type |-> "write"]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_locked,
                 client_prewritten, key_data, reads, msgs>>

\* Lock TTL expiry: primary lock rolled back
RollbackPrimary(k) ==
  /\ \E l \in key_lock[k] :
       /\ l.primary = k
       /\ key_lock' = [key_lock EXCEPT ![k] = {}]
       /\ key_write' = [key_write EXCEPT ![k] =
             @ \cup {[ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_locked,
                 client_prewritten, key_data, reads, msgs>>

ResolveSecondary(k) ==
  /\ \E l \in key_lock[k] :
       LET p  == l.primary
           cw == {w \in key_write[p] : w.start_ts = l.ts /\ w.type = "write"}
           rb == [ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"]
       IN
       /\ p # k
       /\ IF cw # {}
            THEN /\ key_lock' = [key_lock EXCEPT ![k] = {}]
                 /\ key_write' = [key_write EXCEPT ![k] =
                       @ \cup {[ts |-> (CHOOSE w \in cw : TRUE).ts,
                                start_ts |-> l.ts, type |-> "write"]}]
            ELSE /\ ~(\E l2 \in key_lock[p] : l2.ts = l.ts)
                 /\ key_lock' = [key_lock EXCEPT ![k] = {}]
                 /\ key_write' = [key_write EXCEPT
                       ![k] = @ \cup {rb},
                       ![p] = IF \E w \in key_write[p] : w.start_ts = l.ts
                                THEN @ ELSE @ \cup {rb}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_locked,
                 client_prewritten, key_data, reads, msgs>>

Terminating ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT : Start(c) \/ GetCommitTs(c) \/ CommitPrimary(c)
  \/ \E c \in CLIENT, k \in KEY :
       \/ ReadKey(c, k)
       \/ OptPrewrite(c, k)
       \/ PessLock(c, k)
       \/ PessPrewrite(c, k)
       \/ CommitSecondary(c, k)
  \/ \E k \in KEY : RollbackPrimary(k) \/ ResolveSecondary(k)
  \/ Terminating

Spec == Init /\ [][Next]_vars

\* ---------------- Invariants ----------------
TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ \A c \in CLIENT :
       /\ client_ts[c].start_ts \in Nat
       /\ client_ts[c].commit_ts \in Nat
       /\ client_ts[c].for_update_ts \in Nat
       /\ client_locked[c] \subseteq KEY
       /\ client_prewritten[c] \subseteq KEY
  /\ \A k \in KEY :
       /\ \A l \in key_lock[k] :
            /\ l.ts \in Nat /\ l.primary \in KEY
            /\ l.type \in LockTypes /\ l.for_update_ts \in Nat
       /\ \A w \in key_write[k] :
            /\ w.ts \in Nat /\ w.start_ts \in Nat
            /\ w.type \in {"write", "rollback"}
       /\ key_data[k] \subseteq Nat
  /\ \A r \in reads :
       r.c \in CLIENT /\ r.k \in KEY /\ r.ts \in Nat /\ r.val \in Nat
  /\ \A m \in msgs :
       /\ m.c \in CLIENT /\ m.type \in {"prewrite", "commit"}
       /\ m.start_ts \in Nat /\ m.commit_ts \in Nat

UniqueCommitOrAbort ==
  /\ \A k \in KEY : \A w1, w2 \in key_write[k] :
       w1.start_ts = w2.start_ts => w1 = w2
  /\ \A c \in CLIENT :
       ~(/\ \E w \in key_write[CLIENT_PRIMARY[c]] :
               w.start_ts = client_ts[c].start_ts /\ w.type = "write"
         /\ \E w \in key_write[CLIENT_PRIMARY[c]] :
               w.start_ts = client_ts[c].start_ts /\ w.type = "rollback")

CommitConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      LET sts == client_ts[c].start_ts
          cts == client_ts[c].commit_ts
      IN
      /\ \E w \in key_write[CLIENT_PRIMARY[c]] :
           w.start_ts = sts /\ w.ts = cts /\ w.type = "write"
      /\ \A k \in CLIENT_WRITE_KEY[c] :
           \/ \E l \in key_lock[k] : l.ts = sts
           \/ \E w \in key_write[k] :
                w.start_ts = sts /\ w.ts = cts /\ w.type = "write"

AbortConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~\E w \in key_write[CLIENT_PRIMARY[c]] :
         w.start_ts = client_ts[c].start_ts /\ w.type = "write"

WriteConsistency ==
  \A k \in KEY : \A w \in Writes(k) :
    /\ w.start_ts \in key_data[k]
    /\ w.ts > w.start_ts

UniqueLockOrWrite ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k], w \in key_write[k] : w.start_ts # l.ts

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    w1.ts = w2.ts => w1 = w2

OptimisticReadSnapshotIsolation ==
  \A r \in reads :
    r.c \in OPTIMISTIC_CLIENT =>
      /\ r.ts = client_ts[r.c].start_ts
      /\ r.val = LatestBefore(r.k, r.ts)

PessimisticReadSnapshotIsolation ==
  \A r \in reads :
    r.c \in PESSIMISTIC_CLIENT =>
      /\ r.ts <= client_ts[r.c].for_update_ts
      /\ r.val = LatestBefore(r.k, r.ts)

MsgTsConsistency ==
  \A m \in msgs :
    /\ m.start_ts = client_ts[m.c].start_ts
    /\ m.type = "commit" =>
         /\ m.commit_ts > m.start_ts
         /\ m.commit_ts = client_ts[m.c].commit_ts
         /\ (m.c \in PESSIMISTIC_CLIENT =>
               m.commit_ts > client_ts[m.c].for_update_ts)

=============================================================================
```