---- MODULE MC ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS k1, k2, c1, c2, c3

CONSTANTS KEY, OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT,
          CLIENT_READ_KEY, CLIENT_WRITE_KEY, CLIENT_PRIMARY

\* ---------------- Configuration definitions ----------------
Keys == {k1, k2}

OptimistiicClient == {c1, c2}

PessimisticClient == {c3}

ClientReadKeys ==
  [c \in {c1, c2, c3} |->
     IF c = c1 THEN {k1}
     ELSE IF c = c2 THEN {k2}
     ELSE {k1, k2}]

ClientWriteKeys ==
  [c \in {c1, c2, c3} |->
     IF c = c1 THEN {k1, k2}
     ELSE IF c = c2 THEN {k1, k2}
     ELSE {k1}]

ClientPrimary ==
  [c \in {c1, c2, c3} |->
     IF c = c1 THEN k1
     ELSE IF c = c2 THEN k2
     ELSE k1]

\* ---------------- System model ----------------
CLIENT == OPTIMISTIC_CLIENT \cup PESSIMISTIC_CLIENT

VARIABLES next_ts, client_state, client_ts, client_read,
          key_lock, key_write, key_data

vars == <<next_ts, client_state, client_ts, client_read,
          key_lock, key_write, key_data>>

States == {"init", "working", "committing", "committed", "aborted"}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

StartTs(c) == client_ts[c].start_ts

OwnLock(c, k) == \E l \in key_lock[k] : l.ts = StartTs(c)

OwnPrewrite(c, k) ==
  \E l \in key_lock[k] : l.ts = StartTs(c) /\ l.type = "prewrite"

HasWriteAfter(k, ts) == \E w \in key_write[k] : w.commit_ts >= ts

LatestCommit(k, ts) ==
  Max({w.commit_ts : w \in {x \in key_write[k] :
                              x.type = "write" /\ x.commit_ts <= ts}} \cup {0})

Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
  /\ client_read = [c \in CLIENT |-> [k \in KEY |-> -1]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]

Start(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_read, key_lock, key_write, key_data>>

Read(c, k) ==
  /\ client_state[c] = "working"
  /\ k \in CLIENT_READ_KEY[c]
  /\ client_read[c][k] = -1
  /\ ~\E l \in key_lock[k] :
        /\ l.type = "prewrite"
        /\ l.ts <= StartTs(c)
        /\ l.ts # StartTs(c)
  /\ client_read' = [client_read EXCEPT ![c][k] = LatestCommit(k, StartTs(c))]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_lock, key_write, key_data>>

LockKey(c, k) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ k \in CLIENT_WRITE_KEY[c]
  /\ key_lock[k] = {}
  /\ ~HasWriteAfter(k, StartTs(c))
  /\ key_lock' = [key_lock EXCEPT ![k] =
        {[ts |-> StartTs(c), primary |-> CLIENT_PRIMARY[c], type |-> "lock_key"]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write, key_data>>

Prewrite(c, k) ==
  /\ client_state[c] = "working"
  /\ k \in CLIENT_WRITE_KEY[c]
  /\ ~OwnPrewrite(c, k)
  /\ IF c \in PESSIMISTIC_CLIENT
       THEN \E l \in key_lock[k] : l.ts = StartTs(c) /\ l.type = "lock_key"
       ELSE /\ key_lock[k] = {}
            /\ ~HasWriteAfter(k, StartTs(c))
  /\ key_lock' = [key_lock EXCEPT ![k] =
        {[ts |-> StartTs(c), primary |-> CLIENT_PRIMARY[c], type |-> "prewrite"]}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \cup {StartTs(c)}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write>>

Abort(c) ==
  /\ client_state[c] = "working"
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ key_lock' = [k \in KEY |-> {l \in key_lock[k] : l.ts # StartTs(c)}]
  /\ key_write' = [k \in KEY |->
        IF k \in CLIENT_WRITE_KEY[c]
          THEN key_write[k] \cup
                 {[start_ts |-> StartTs(c), commit_ts |-> StartTs(c),
                   type |-> "rollback"]}
          ELSE key_write[k]]
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_data>>

AllRead(c) == \A k \in CLIENT_READ_KEY[c] : client_read[c][k] # -1

CommitReadOnly(c) ==
  /\ client_state[c] = "working"
  /\ CLIENT_WRITE_KEY[c] = {}
  /\ AllRead(c)
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write, key_data>>

CommitPrimary(c) ==
  LET p == CLIENT_PRIMARY[c] IN
  /\ client_state[c] = "working"
  /\ CLIENT_WRITE_KEY[c] # {}
  /\ AllRead(c)
  /\ \A k \in CLIENT_WRITE_KEY[c] : OwnPrewrite(c, k)
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # StartTs(c)}]
  /\ key_write' = [key_write EXCEPT ![p] = @ \cup
        {[start_ts |-> StartTs(c), commit_ts |-> next_ts, type |-> "write"]}]
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_read, key_data>>

CommitSecondary(c, k) ==
  /\ client_state[c] = "committing"
  /\ k \in CLIENT_WRITE_KEY[c] \ {CLIENT_PRIMARY[c]}
  /\ OwnLock(c, k)
  /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # StartTs(c)}]
  /\ key_write' = [key_write EXCEPT ![k] = @ \cup
        {[start_ts |-> StartTs(c), commit_ts |-> client_ts[c].commit_ts,
          type |-> "write"]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_data>>

Finish(c) ==
  /\ client_state[c] = "committing"
  /\ \A k \in CLIENT_WRITE_KEY[c] : ~OwnLock(c, k)
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write, key_data>>

Done ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ Start(c)
       \/ Abort(c)
       \/ CommitReadOnly(c)
       \/ CommitPrimary(c)
       \/ Finish(c)
       \/ \E k \in KEY : Read(c, k) \/ LockKey(c, k)
                         \/ Prewrite(c, k) \/ CommitSecondary(c, k)
  \/ Done

Spec == Init /\ [][Next]_vars

\* ---------------- Invariants ----------------
TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> States]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
  /\ client_read \in [CLIENT -> [KEY -> Int]]
  /\ \A k \in KEY :
       /\ \A l \in key_lock[k] :
            /\ l.ts \in Nat /\ l.primary \in KEY
            /\ l.type \in {"lock_key", "prewrite"}
       /\ \A w \in key_write[k] :
            /\ w.start_ts \in Nat /\ w.commit_ts \in Nat
            /\ w.type \in {"write", "rollback"}
       /\ key_data[k] \subseteq Nat
       /\ Cardinality(key_lock[k]) <= 1

UniqueCommitOrAbort ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    w1.start_ts = w2.start_ts => w1 = w2

CommitConsistency ==
  \A c \in CLIENT :
    (client_state[c] = "committed" /\ CLIENT_WRITE_KEY[c] # {}) =>
      \A k \in CLIENT_WRITE_KEY[c] :
        \E w \in key_write[k] :
          /\ w.start_ts = StartTs(c)
          /\ w.type = "write"
          /\ w.commit_ts = client_ts[c].commit_ts

AbortConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY :
        /\ ~\E w \in key_write[k] : w.start_ts = StartTs(c) /\ w.type = "write"
        /\ ~OwnLock(c, k)

WriteConsistency ==
  \A k \in KEY : \A w \in key_write[k] :
    w.type = "write" => w.start_ts \in key_data[k]

UniqueLockOrWrite ==
  \A k \in KEY : \A l \in key_lock[k] :
    ~\E w \in key_write[k] : w.start_ts = l.ts

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    w1.commit_ts = w2.commit_ts => w1 = w2

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : \A k \in KEY :
    client_read[c][k] # -1 =>
      client_read[c][k] = LatestCommit(k, StartTs(c))

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : \A k \in KEY :
    client_read[c][k] # -1 =>
      client_read[c][k] = LatestCommit(k, StartTs(c))

MsgTsConsistency ==
  /\ \A c \in CLIENT :
       /\ client_state[c] # "init" => StartTs(c) > 0 /\ StartTs(c) < next_ts
       /\ client_state[c] \in {"committing", "committed"} /\ CLIENT_WRITE_KEY[c] # {} =>
            client_ts[c].commit_ts > StartTs(c)
  /\ \A ca, cb \in CLIENT :
       (ca # cb /\ client_state[ca] # "init" /\ client_state[cb] # "init") =>
         StartTs(ca) # StartTs(cb)
  /\ \A k \in KEY : \A w \in key_write[k] : w.commit_ts >= w.start_ts

====