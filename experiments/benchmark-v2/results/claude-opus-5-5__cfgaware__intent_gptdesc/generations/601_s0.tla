---------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Model values used to build the concrete client set
CONSTANTS c1, c2

\* Abstract parameters (bound in the configuration via substitution)
CONSTANTS KEY, CLIENT, CLIENT_PRIMARY_KEY

\* Concrete definitions bound to the parameters by the configuration
Key == {"k1", "k2"}
Client == {c1, c2}
ClientPrimaryKey == [c \in Client |-> IF c = c1 THEN "k1" ELSE "k2"]

ASSUME CLIENT_PRIMARY_KEY \in [CLIENT -> KEY]

VARIABLES
    next_ts,        \* timestamp oracle: strictly increasing
    client_state,   \* state of each client's transaction
    client_ts,      \* start_ts and commit_ts of each client's transaction
    client_key,     \* primary, secondary and still-pending keys
    key_lock,       \* key -> set of lock records
    key_write,      \* key -> sequence of write / rollback records
    key_data        \* key -> set of start_ts of prewritten data

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_lock, key_write, key_data>>
vars == <<next_ts, client_vars, key_vars>>

ClientStates ==
    {"init", "working", "prewriting", "committing", "committed", "aborted"}
LockTypes == {"prewrite_primary", "prewrite_secondary"}
WriteTypes == {"write", "rollback"}

-----------------------------------------------------------------------------
\* Helpers

WriteRecs(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

WritesWithStartTS(k, ts) == {w \in WriteRecs(k) : w.start_ts = ts}

HasLockWithTS(k, ts) == \E l \in key_lock[k] : l.ts = ts

\* A key can be locked at ts if there is no lock and no newer write record.
CanLockKey(k, ts) ==
    /\ key_lock[k] = {}
    /\ \A w \in WriteRecs(k) : w.ts < ts

HasStaleLock(k, ts) == \E l \in key_lock[k] : l.ts <= ts

\* Resolve a lock on key k whose start_ts is not newer than ts, using
\* the state of its primary key as the single source of truth.
CleanupStaleLock(k, ts) ==
    \E l \in key_lock[k] :
        /\ l.ts <= ts
        /\ LET p == l.primary IN
           IF HasLockWithTS(p, l.ts)
           THEN \* primary still locked: roll back the primary
                /\ key_lock' = [key_lock EXCEPT ![p] =
                                  {pl \in @ : pl.ts # l.ts}]
                /\ key_data' = [key_data EXCEPT ![p] = @ \ {l.ts}]
                /\ key_write' = [key_write EXCEPT ![p] =
                     Append(@, [ts |-> l.ts, start_ts |-> l.ts,
                                type |-> "rollback"])]
           ELSE
             LET cw == {w \in WritesWithStartTS(p, l.ts) : w.type = "write"}
             IN IF cw # {}
                THEN \* primary committed: roll forward this secondary
                     LET w == CHOOSE x \in cw : TRUE IN
                     /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                     /\ key_write' = [key_write EXCEPT ![k] =
                          Append(@, [ts |-> w.ts, start_ts |-> l.ts,
                                     type |-> "write"])]
                     /\ UNCHANGED key_data
                ELSE \* primary rolled back: roll back this secondary
                     /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                     /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
                     /\ key_write' = [key_write EXCEPT ![k] =
                          Append(@, [ts |-> l.ts, start_ts |-> l.ts,
                                     type |-> "rollback"])]

-----------------------------------------------------------------------------
Init ==
    /\ next_ts = 0
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |->
                       [primary   |-> CLIENT_PRIMARY_KEY[c],
                        secondary |-> KEY \ {CLIENT_PRIMARY_KEY[c]},
                        pending   |-> KEY]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> << >>]
    /\ key_data = [k \in KEY |-> {}]

\* Obtain a start timestamp.
Start(c) ==
    /\ client_state[c] = "init"
    /\ next_ts' = next_ts + 1
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts + 1]
    /\ UNCHANGED <<client_key, key_vars>>

\* Read a key at start_ts; a stale lock blocking the read is resolved.
Get(c) ==
    LET st == client_ts[c].start_ts IN
    /\ client_state[c] = "working"
    /\ \E k \in KEY :
         /\ HasStaleLock(k, st)
         /\ CleanupStaleLock(k, st)
    /\ UNCHANGED <<next_ts, client_vars>>

StartPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

\* Prewrite (lock) keys, primary first; abort on conflict.
Prewrite(c) ==
    LET st == client_ts[c].start_ts
        p  == client_key[c].primary
    IN
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending # {}
    /\ \E k \in client_key[c].pending :
         /\ (p \in client_key[c].pending => k = p)
         /\ IF CanLockKey(k, st)
            THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                      {[ts |-> st, primary |-> p,
                        type |-> IF k = p THEN "prewrite_primary"
                                          ELSE "prewrite_secondary"]}]
                 /\ key_data' = [key_data EXCEPT ![k] = @ \cup {st}]
                 /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
                 /\ UNCHANGED <<key_write, client_state>>
            ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
                 /\ UNCHANGED <<client_key, key_vars>>
    /\ UNCHANGED <<next_ts, client_ts>>

\* All keys prewritten: obtain a commit timestamp.
Commit(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending = {}
    /\ next_ts' = next_ts + 1
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts + 1]
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ UNCHANGED <<client_key, key_vars>>

\* Commit the primary: the atomic commit point of the transaction.
CommitPrimary(c) ==
    LET st == client_ts[c].start_ts
        ct == client_ts[c].commit_ts
        p  == client_key[c].primary
    IN
    /\ client_state[c] = "committing"
    /\ IF HasLockWithTS(p, st)
       THEN /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # st}]
            /\ key_write' = [key_write EXCEPT ![p] =
                 Append(@, [ts |-> ct, start_ts |-> st, type |-> "write"])]
            /\ client_state' = [client_state EXCEPT ![c] = "committed"]
            /\ UNCHANGED key_data
       ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
            /\ UNCHANGED key_vars
    /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* Secondaries accept the commit timestamp assigned via the primary.
CommitSecondary(c) ==
    LET st == client_ts[c].start_ts
        ct == client_ts[c].commit_ts
    IN
    /\ client_state[c] = "committed"
    /\ \E k \in client_key[c].secondary :
         /\ HasLockWithTS(k, st)
         /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # st}]
         /\ key_write' = [key_write EXCEPT ![k] =
              Append(@, [ts |-> ct, start_ts |-> st, type |-> "write"])]
    /\ UNCHANGED <<next_ts, client_vars, key_data>>

ClientOp(c) ==
    \/ Start(c)
    \/ Get(c)
    \/ StartPrewrite(c)
    \/ Prewrite(c)
    \/ Commit(c)
    \/ CommitPrimary(c)
    \/ CommitSecondary(c)

Done ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E c \in CLIENT : ClientOp(c)
    \/ Done

\* Liveness assumption: fair scheduling of every client (no permanent failure).
PercolatorSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in CLIENT : WF_vars(ClientOp(c))

-----------------------------------------------------------------------------
\* Safety properties

TypeInvariant ==
    /\ next_ts \in Nat
    /\ DOMAIN client_state = CLIENT
    /\ DOMAIN client_ts = CLIENT
    /\ DOMAIN client_key = CLIENT
    /\ DOMAIN key_lock = KEY
    /\ DOMAIN key_write = KEY
    /\ DOMAIN key_data = KEY
    /\ \A c \in CLIENT :
         /\ client_state[c] \in ClientStates
         /\ client_ts[c].start_ts \in Nat
         /\ client_ts[c].commit_ts \in Nat
         /\ client_key[c].primary \in KEY
         /\ client_key[c].secondary \subseteq KEY
         /\ client_key[c].pending \subseteq KEY
    /\ \A k \in KEY :
         /\ \A l \in key_lock[k] :
              /\ l.ts \in Nat
              /\ l.primary \in KEY
              /\ l.type \in LockTypes
         /\ key_write[k] \in Seq(WriteRecs(k))
         /\ \A w \in WriteRecs(k) :
              /\ w.ts \in Nat
              /\ w.start_ts \in Nat
              /\ w.type \in WriteTypes
         /\ key_data[k] \subseteq Nat

\* Write records of a key are totally ordered by their timestamps (no lost update).
WriteConsistency ==
    \A k \in KEY :
      \A i, j \in DOMAIN key_write[k] :
        i < j => key_write[k][i].ts < key_write[k][j].ts

\* At most one lock per key; a lock has its data and no newer write exists.
LockConsistency ==
    \A k \in KEY :
      /\ Cardinality(key_lock[k]) <= 1
      /\ \A l \in key_lock[k] :
           /\ l.ts \in key_data[k]
           /\ \A w \in WriteRecs(k) : w.ts < l.ts
           /\ (l.type = "prewrite_primary") <=> (l.primary = k)

\* A committed transaction: primary committed at commit_ts; every secondary
\* is either committed at commit_ts or still locked (to be rolled forward);
\* nothing of it was rolled back.
CommittedConsistency ==
    \A c \in CLIENT :
      LET st  == client_ts[c].start_ts
          ct  == client_ts[c].commit_ts
          rec == [ts |-> ct, start_ts |-> st, type |-> "write"]
      IN client_state[c] = "committed" =>
           /\ st < ct
           /\ rec \in WriteRecs(client_key[c].primary)
           /\ \A k \in client_key[c].secondary :
                \/ HasLockWithTS(k, st)
                \/ rec \in WriteRecs(k)
           /\ \A k \in KEY :
                \A w \in WritesWithStartTS(k, st) : w.type = "write"

\* An aborted transaction never makes any write visible.
AbortedConsistency ==
    \A c \in CLIENT :
      client_state[c] = "aborted" =>
        \A k \in KEY :
          \A w \in WritesWithStartTS(k, client_ts[c].start_ts) :
            w.type = "rollback"

\* Atomicity: a transaction that was rolled back on some key is
\* committed on no key.
RollbackConsistency ==
    \A ka, kb \in KEY :
      \A wa \in WriteRecs(ka), wb \in WriteRecs(kb) :
        (wa.type = "rollback" /\ wb.start_ts = wa.start_ts)
           => wb.type = "rollback"

\* Each transaction writes a key at most once, and timestamps are unique.
UniqueWrite ==
    \A k \in KEY :
      \A i, j \in DOMAIN key_write[k] :
        i # j =>
          /\ key_write[k][i].start_ts # key_write[k][j].start_ts
          /\ key_write[k][i].ts # key_write[k][j].ts

\* Two committed transactions writing a common key never have overlapping
\* [start_ts, commit_ts] intervals (first-committer-wins snapshot isolation),
\* so reads at start_ts see a consistent committed prefix.
SnapshotIsolation ==
    \A ca, cb \in CLIENT :
      ( /\ ca # cb
        /\ client_state[ca] = "committed"
        /\ client_state[cb] = "committed"
        /\ (client_key[ca].secondary \cup {client_key[ca].primary})
             \cap (client_key[cb].secondary \cup {client_key[cb].primary}) # {} )
      => \/ client_ts[ca].commit_ts < client_ts[cb].start_ts
         \/ client_ts[cb].commit_ts < client_ts[ca].start_ts

\* Liveness: every transaction eventually commits or aborts.
Termination ==
    <>(\A c \in CLIENT : client_state[c] \in {"committed", "aborted"})

=============================================================================