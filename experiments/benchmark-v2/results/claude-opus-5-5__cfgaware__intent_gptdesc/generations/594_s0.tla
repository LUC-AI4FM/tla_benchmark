```tla
rimaryRecvPropose)

Spec == Init /\ [][Next]_vars /\ Fairness

\* ---------------- Helpers over the commit history ----------------
InHist(c) == \E i \in DOMAIN hist : hist[i].client = c

\* Index of last committed transaction among hist[1..n] that wrote k (0 if none)
LastWriteIdx(k, n) ==
    LET S == {i \in 1..n : k \in hist[i].writes}
    IN IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i

\* Version of k visible just before the i-th commit
TsBefore(k, i) ==
    LET j == LastWriteIdx(k, i - 1)
    IN IF j = 0 THEN 0 ELSE hist[j].ts

\* ---------------- Invariants ----------------
TypeOK ==
    /\ kv \in [KEY -> [val : CLIENT \cup {NoClient}, ts : Nat]]
    /\ lock \in [KEY -> CLIENT \cup {NoClient}]
    /\ cstate \in [CLIENT -> ClientStates]
    /\ pstate \in [CLIENT -> PrimaryStates]
    /\ granted \in [CLIENT -> SUBSET KEY]
    /\ creads \in [CLIENT -> [KEY -> Int]]
    /\ nextTs \in Nat \ {0}
    /\ \A m \in msgs : m.type \in MsgTypes /\ m.client \in CLIENT
    /\ \A i \in DOMAIN hist : /\ hist[i].client \in CLIENT
                              /\ hist[i].writes \subseteq KEY

UniqueCommitOrAbort ==
    /\ \A i, j \in DOMAIN hist : hist[i].client = hist[j].client => i = j
    /\ \A c \in CLIENT :
         /\ cstate[c] = "committed" => InHist(c)
         /\ cstate[c] = "aborted" => ~InHist(c)
    /\ \A m1, m2 \in msgs :
         (m1.type = "Decision" /\ m2.type = "Decision" /\ m1.client = m2.client)
            => m1.commit = m2.commit

CommitConsistency ==
    \A i \in DOMAIN hist :
       /\ hist[i].ts = i
       /\ hist[i].writes = W(hist[i].client)
       /\ cstate[hist[i].client] \in {"proposed", "committed"}
       /\ pstate[hist[i].client] = "done"
       \* all writes of a committed transaction became visible together
       /\ \A k \in hist[i].writes : kv[k].ts >= hist[i].ts

AbortConsistency ==
    \A c \in CLIENT :
       cstate[c] = "aborted" =>
          /\ ~InHist(c)
          /\ \A k \in KEY : kv[k].val # c

WriteConsistency ==
    /\ nextTs = Len(hist) + 1
    /\ \A k \in KEY :
         LET i == LastWriteIdx(k, Len(hist))
         IN /\ kv[k].ts = (IF i = 0 THEN 0 ELSE hist[i].ts)
            /\ kv[k].val = (IF i = 0 THEN NoClient ELSE hist[i].client)

UniqueLockOrWrite ==
    /\ \A k \in KEY :
         lock[k] # NoClient =>
            /\ k \in RW(lock[k])
            /\ cstate[lock[k]] # "committed"
    /\ \A c \in PESSIMISTIC_CLIENT :
         (cstate[c] \in {"locking", "reading", "proposed"} /\ pstate[c] # "done")
            => \A k \in granted[c] : lock[k] = c

UniqueWrite ==
    \A i, j \in DOMAIN hist :
       i # j => /\ hist[i].ts # hist[j].ts
                /\ hist[i].client # hist[j].client

OptimisticReadSnapshotIsolation ==
    \A i \in DOMAIN hist :
       hist[i].client \in OPTIMISTIC_CLIENT =>
          \A k \in R(hist[i].client) : hist[i].reads[k] = TsBefore(k, i)

PessimisticReadSnapshotIsolation ==
    /\ \A i \in DOMAIN hist :
         hist[i].client \in PESSIMISTIC_CLIENT =>
            \A k \in R(hist[i].client) : hist[i].reads[k] = TsBefore(k, i)
    /\ \A c \in PESSIMISTIC_CLIENT :
         (cstate[c] \in {"reading", "proposed"} /\ pstate[c] # "done")
            => \A k \in R(c) \cap W(c) :
                  creads[c][k] >= 0 => kv[k].ts = creads[c][k]

MsgTsConsistency ==
    \A m \in msgs :
       /\ m.type = "ReadResp" => /\ m.ts <= kv[m.key].ts
                                 /\ m.ts < nextTs
       /\ m.type = "Prepare" => /\ m.rts < nextTs
                                /\ m.rts <= kv[m.key].ts
       /\ m.type = "Decision" => (m.commit => m.ts < nextTs)

\* Serializability: committed transactions are equivalent to the serial
\* execution in commit order (every read saw the latest prior committed write)
Serializability ==
    \A i \in DOMAIN hist :
       \A k \in R(hist[i].client) : hist[i].reads[k] = TsBefore(k, i)

\* No lost updates: a committed read-modify-write saw the previous version
NoLostUpdate ==
    \A i \in DOMAIN hist :
       \A k \in hist[i].writes \cap R(hist[i].client) :
          hist[i].reads[k] = TsBefore(k, i)

\* ---------------- Liveness ----------------
Termination == <>(\A c \in CLIENT : cstate[c] \in {"committed", "aborted"})

LocksEventuallyReleased == <>[](\A k \in KEY : lock[k] = NoClient)

=============================================================================
```