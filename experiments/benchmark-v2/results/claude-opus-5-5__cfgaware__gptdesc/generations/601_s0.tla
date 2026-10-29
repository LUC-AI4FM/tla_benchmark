---------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS c1, c2
CONSTANTS Key, Client, ClientPrimaryKey

KEY == {1, 2}
CLIENT == {c1, c2}
CLIENT_PRIMARY_KEY == [c \in CLIENT |-> IF c = c1 THEN 1 ELSE 2]

ASSUME ClientPrimaryKey \in [Client -> Key]

VARIABLES next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data

vars == <<next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data>>

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

TypeInvariant ==
  /\ next_ts \in Nat
  /\ client_state \in [Client -> States]
  /\ client_ts \in [Client -> [start_ts : Nat, commit_ts : Nat]]
  /\ client_key \in [Client -> [primary : Key, secondary : SUBSET Key, pending : SUBSET Key]]
  /\ key_lock \in [Key -> SUBSET [ts : Nat, primary : Key]]
  /\ key_write \in [Key -> SUBSET [start_ts : Nat, commit_ts : Nat, type : {"write", "rollback"}]]
  /\ key_data \in [Key -> SUBSET Nat]

Init ==
  /\ next_ts = 1
  /\ client_state = [c \in Client |-> "init"]
  /\ client_ts = [c \in Client |-> [start_ts |-> 0, commit_ts |-> 0]]
  /\ client_key = [c \in Client |->
                    [primary |-> ClientPrimaryKey[c],
                     secondary |-> Key \ {ClientPrimaryKey[c]},
                     pending |-> {}]]
  /\ key_lock = [k \in Key |-> {}]
  /\ key_write = [k \in Key |-> {}]
  /\ key_data = [k \in Key |-> {}]

HasLock(k, ts) == \E l \in key_lock[k] : l.ts = ts

CanLock(k, ts) ==
  /\ key_lock[k] = {}
  /\ \A w \in key_write[k] : w.commit_ts < ts

Start(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, key_lock, key_write, key_data>>

\* Resolve a stale lock left by an older transaction.
Cleanup(c, k) ==
  /\ client_state[c] = "working"
  /\ \E l \in key_lock[k] :
       /\ l.ts < client_ts[c].start_ts
       /\ LET p == l.primary IN
          IF \E w \in key_write[p] : w.start_ts = l.ts /\ w.type = "write"
          THEN LET w == CHOOSE w \in key_write[p] : w.start_ts = l.ts /\ w.type = "write"
               IN /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                  /\ key_write' = [key_write EXCEPT ![k] =
                        @ \cup {[start_ts |-> l.ts, commit_ts |-> w.commit_ts, type |-> "write"]}]
                  /\ UNCHANGED key_data
          ELSE IF HasLock(p, l.ts)
          THEN LET pl == CHOOSE pl \in key_lock[p] : pl.ts = l.ts
               IN /\ key_lock' = [key_lock EXCEPT ![p] = @ \ {pl}]
                  /\ key_write' = [key_write EXCEPT ![p] =
                        @ \cup {[start_ts |-> l.ts, commit_ts |-> l.ts, type |-> "rollback"]}]
                  /\ key_data' = [key_data EXCEPT ![p] = @ \ {l.ts}]
          ELSE /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
               /\ key_write' = [key_write EXCEPT ![k] =
                     @ \cup {[start_ts |-> l.ts, commit_ts |-> l.ts, type |-> "rollback"]}]
               /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key>>

BeginPrewrite(c) ==
  /\ client_state[c] = "working"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].pending = {client_key[c].primary}]
  /\ UNCHANGED <<next_ts, client_ts, key_lock, key_write, key_data>>

PrewriteKey(c, k) ==
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].pending
  /\ LET ts == client_ts[c].start_ts IN
     IF CanLock(k, ts)
     THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                @ \cup {[ts |-> ts, primary |-> client_key[c].primary]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
          /\ client_key' = [client_key EXCEPT ![c].pending =
                IF k = client_key[c].primary
                THEN client_key[c].secondary
                ELSE @ \ {k}]
          /\ UNCHANGED client_state
     ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
          /\ UNCHANGED <<key_lock, key_data, client_key>>
  /\ UNCHANGED <<next_ts, client_ts, key_write>>

CommitPrimary(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].pending = {}
  /\ LET ts == client_ts[c].start_ts
         p  == client_key[c].primary
     IN IF HasLock(p, ts)
        THEN LET l == CHOOSE l \in key_lock[p] : l.ts = ts
             IN /\ key_lock' = [key_lock EXCEPT ![p] = @ \ {l}]
                /\ key_write' = [key_write EXCEPT ![p] =
                      @ \cup {[start_ts |-> ts, commit_ts |-> next_ts, type |-> "write"]}]
                /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
                /\ next_ts' = next_ts + 1
                /\ client_state' = [client_state EXCEPT ![c] = "committing"]
                /\ client_key' = [client_key EXCEPT ![c].pending = client_key[c].secondary]
        ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
             /\ UNCHANGED <<key_lock, key_write, client_ts, next_ts, client_key>>
  /\ UNCHANGED key_data

CommitSecondary(c, k) ==
  /\ client_state[c] = "committing"
  /\ k \in client_key[c].pending
  /\ LET ts == client_ts[c].start_ts IN
     IF HasLock(k, ts)
     THEN LET l == CHOOSE l \in key_lock[k] : l.ts = ts
          IN /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
             /\ key_write' = [key_write EXCEPT ![k] =
                   @ \cup {[start_ts |-> ts, commit_ts |-> client_ts[c].commit_ts, type |-> "write"]}]
     ELSE UNCHANGED <<key_lock, key_write>>
  /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_data>>

FinishCommit(c) ==
  /\ client_state[c] = "committing"
  /\ client_key[c].pending = {}
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_lock, key_write, key_data>>

Done ==
  /\ \A c \in Client : client_state[c] \in {"committed", "aborted"}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in Client :
       \/ Start(c)
       \/ BeginPrewrite(c)
       \/ CommitPrimary(c)
       \/ FinishCommit(c)
       \/ \E k \in Key : Cleanup(c, k) \/ PrewriteKey(c, k) \/ CommitSecondary(c, k)
  \/ Done

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

WriteConsistency ==
  \A k \in Key : \A w \in key_write[k] :
    /\ w.type = "write" => (w.start_ts < w.commit_ts /\ w.start_ts \in key_data[k])
    /\ w.type = "rollback" => (w.start_ts = w.commit_ts /\ w.start_ts \notin key_data[k])

LockConsistency ==
  \A k \in Key :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] :
         /\ l.ts \in key_data[k]
         /\ ~\E w \in key_write[k] : w.start_ts = l.ts

CommittedConsistency ==
  \A c \in Client : client_state[c] = "committed" =>
    \A k \in Key :
      /\ [start_ts |-> client_ts[c].start_ts,
          commit_ts |-> client_ts[c].commit_ts,
          type |-> "write"] \in key_write[k]
      /\ ~HasLock(k, client_ts[c].start_ts)

AbortedConsistency ==
  \A c \in Client : client_state[c] = "aborted" =>
    \A k \in Key : \A w \in key_write[k] :
      w.start_ts = client_ts[c].start_ts => w.type = "rollback"

RollbackConsistency ==
  \A k1, k2 \in Key :
    \A w1 \in key_write[k1], w2 \in key_write[k2] :
      w1.start_ts = w2.start_ts => w1.type = w2.type

UniqueWrite ==
  \A k \in Key : \A w1, w2 \in key_write[k] :
    /\ w1.commit_ts = w2.commit_ts => w1 = w2
    /\ w1.start_ts = w2.start_ts => w1 = w2

SnapshotIsolation ==
  \A k \in Key : \A w1, w2 \in key_write[k] :
    (w1 /= w2 /\ w1.type = "write" /\ w2.type = "write") =>
      (w1.commit_ts < w2.start_ts \/ w2.commit_ts < w1.start_ts)

=============================================================================