```tla
    LET i == m.dest IN
    /\ m.term > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
    /\ role'        = [role EXCEPT ![i] = Follower]
    /\ votedFor'    = [votedFor EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, votesGranted, nextIndex, matchIndex, up,
                   msgs, committed, lossCount, crashCount>>

\* Vote request handling: grant only in the current term, only once per term,
\* and only to a candidate whose log is at least as up-to-date.
HandleRVReq(m) ==
    LET i     == m.dest
        j     == m.src
        logOk == \/ m.lastLogTerm > LastTerm(log[i])
                 \/ /\ m.lastLogTerm = LastTerm(log[i])
                    /\ m.lastLogIndex >= Len(log[i])
        grant == /\ m.term = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN
    /\ m.type = "RVReq"
    /\ m.term <= currentTerm[i]
    /\ votedFor' = IF grant THEN [votedFor EXCEPT ![i] = j] ELSE votedFor
    /\ Reply([type    |-> "RVResp",
              term    |-> currentTerm[i],
              src     |-> i,
              dest    |-> j,
              granted |-> grant], m)
    /\ UNCHANGED <<currentTerm, role, log, commitIndex, votesGranted, nextIndex,
                   matchIndex, up, committed, lossCount, crashCount>>

\* Vote response handling.
HandleRVResp(m) ==
    LET i == m.dest IN
    /\ m.type = "RVResp"
    /\ m.term <= currentTerm[i]
    /\ votesGranted' =
          IF m.term = currentTerm[i] /\ role[i] = Candidate /\ m.granted
          THEN [votesGranted EXCEPT ![i] = @ \cup {m.src}]
          ELSE votesGranted
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex, nextIndex,
                   matchIndex, up, committed, lossCount, crashCount>>

\* Reject an append request from a stale-term leader.
RejectStaleAE(m) ==
    LET i == m.dest IN
    /\ m.type = "AEReq"
    /\ m.term < currentTerm[i]
    /\ Reply([type       |-> "AEResp",
              term       |-> currentTerm[i],
              src        |-> i,
              dest       |-> m.src,
              success    |-> FALSE,
              matchIndex |-> 0], m)
    /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex, votesGranted,
                   nextIndex, matchIndex, up, committed, lossCount, crashCount>>

\* Reject an append request from the current leader because the logs
\* do not match at prevIndex.
RejectMismatchAE(m) ==
    LET i    == m.dest
        prev == m.prevIndex
    IN
    /\ m.type = "AEReq"
    /\ m.term = currentTerm[i]
    /\ ~(prev = 0 \/ (prev <= Len(log[i]) /\ log[i][prev].term = m.prevTerm))
    /\ role' = [role EXCEPT ![i] = Follower]
    /\ Reply([type       |-> "AEResp",
              term       |-> currentTerm[i],
              src        |-> i,
              dest       |-> m.src,
              success    |-> FALSE,
              matchIndex |-> 0], m)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted,
                   nextIndex, matchIndex, up, committed, lossCount, crashCount>>

\* Accept an append request. Truncate any conflicting suffix to repair the
\* log, append the new entries, and advance the commit index only over the
\* entries that were verified.
AcceptAE(m) ==
    LET i      == m.dest
        prev   == m.prevIndex
        idx    == prev + 1
        newLog == IF m.entries = << >>
                  THEN log[i]
                  ELSE IF Len(log[i]) >= idx /\ log[i][idx].term = m.entries[1].term
                       THEN log[i]
                       ELSE SubSeq(log[i], 1, prev) \o m.entries
        mIdx   == prev + Len(m.entries)
    IN
    /\ m.type = "AEReq"
    /\ m.term = currentTerm[i]
    /\ \/ prev = 0
       \/ /\ prev <= Len(log[i])
          /\ log[i][prev].term = m.prevTerm
    /\ role'        = [role EXCEPT ![i] = Follower]
    /\ log'         = [log EXCEPT ![i] = newLog]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(@, Min(m.commit, mIdx))]
    /\ Reply([type       |-> "AEResp",
              term       |-> currentTerm[i],
              src        |-> i,
              dest       |-> m.src,
              success    |-> TRUE,
              matchIndex |-> mIdx], m)
    /\ UNCHANGED <<currentTerm, votedFor, votesGranted, nextIndex, matchIndex,
                   up, committed, lossCount, crashCount>>

\* Append response handling by the leader.
HandleAEResp(m) ==
    LET i == m.dest
        j == m.src
    IN
    /\ m.type = "AEResp"
    /\ m.term <= currentTerm[i]
    /\ IF m.term = currentTerm[i] /\ role[i] = Leader
       THEN IF m.success
            THEN LET newMatch == Max(matchIndex[i][j], m.matchIndex) IN
                 /\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatch]
                 /\ nextIndex'  = [nextIndex EXCEPT ![i][j] = newMatch + 1]
            ELSE /\ nextIndex'  = [nextIndex EXCEPT ![i][j] = Max(@ - 1, 1)]
                 /\ UNCHANGED matchIndex
       ELSE UNCHANGED <<nextIndex, matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex, votesGranted,
                   up, committed, lossCount, crashCount>>

\* A running server receives some message addressed to it.
Receive(m) ==
    /\ m \in msgs
    /\ up[m.dest]
    /\ \/ UpdateTerm(m)
       \/ HandleRVReq(m)
       \/ HandleRVResp(m)
       \/ RejectStaleAE(m)
       \/ RejectMismatchAE(m)
       \/ AcceptAE(m)
       \/ HandleAEResp(m)

----------------------------------------------------------------------------
(* Faults: bounded message loss, crashes, and recoveries *)

DropMessage(m) ==
    /\ m \in msgs
    /\ lossCount < MaxLoss
    /\ Discard(m)
    /\ lossCount' = lossCount + 1
    /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex, votesGranted,
                   nextIndex, matchIndex, up, committed, crashCount>>

\* A crash keeps persistent state (term, vote, log) and loses volatile state.
Crash(i) ==
    /\ up[i]
    /\ crashCount < MaxCrashes
    /\ up'           = [up EXCEPT ![i] = FALSE]
    /\ role'         = [role EXCEPT ![i] = Follower]
    /\ commitIndex'  = [commitIndex EXCEPT ![i] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'    = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'   = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ crashCount'   = crashCount + 1
    /\ UNCHANGED <<currentTerm, votedFor, log, msgs, committed, lossCount>>

Restart(i) ==
    /\ ~up[i]
    /\ up' = [up EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex, votesGranted,
                   nextIndex, matchIndex, msgs, committed, lossCount, crashCount>>

----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ \E i \in Server :
          \/ Timeout(i)
          \/ BecomeLeader(i)
          \/ AdvanceCommitIndex(i)
          \/ Crash(i)
          \/ Restart(i)
    \/ \E i, j \in Server : RequestVote(i, j) \/ AppendEntries(i, j)
    \/ \E i \in Server, v \in Value : ClientRequest(i, v)
    \/ \E m \in msgs : Receive(m) \/ DropMessage(m)

\* Fairness for protocol progress. Timeouts, crashes, and message loss carry
\* no fairness, so the environment may always disrupt them.
Fairness ==
    /\ \A i \in Server :
          /\ WF_vars(BecomeLeader(i))
          /\ WF_vars(AdvanceCommitIndex(i))
          /\ WF_vars(\E m \in msgs : m.dest = i /\ Receive(m))
    /\ \A i, j \in Server :
          /\ WF_vars(RequestVote(i, j))
          /\ WF_vars(AppendEntries(i, j))
    /\ \A i \in Server, v \in Value : WF_vars(ClientRequest(i, v))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ currentTerm  \in [Server -> 0..MaxTerm]
    /\ role         \in [Server -> {Follower, Candidate, Leader}]
    /\ votedFor     \in [Server -> Server \cup {Nil}]
    /\ log          \in [Server -> BoundedLogs]
    /\ commitIndex  \in [Server -> 0..MaxLogLen]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ nextIndex    \in [Server -> [Server -> 1..(MaxLogLen + 1)]]
    /\ matchIndex   \in [Server -> [Server -> 0..MaxLogLen]]
    /\ up           \in [Server -> BOOLEAN]
    /\ msgs         \subseteq Message
    /\ committed    \subseteq CommitRec
    /\ lossCount    \in 0..MaxLoss
    /\ crashCount   \in 0..MaxCrashes

----------------------------------------------------------------------------
(* Safety invariants *)

EntryOf(c) == [term |-> c.term, value |-> c.value]

HasEntry(i, c) ==
    /\ Len(log[i]) >= c.index
    /\ log[i][c.index] = EntryOf(c)

\* At most one leader per term.
ElectionSafety ==
    \A i, j \in Server :
        (role[i] = Leader /\ role[j] = Leader /\ currentTerm[i] = currentTerm[j])
            => i = j

\* Same index and term implies identical prefixes.
LogMatching ==
    \A i, j \in Server : \A n \in 1..MaxLogLen :
        (/\ n <= Len(log[i])
         /\ n <= Len(log[j])
         /\ log[i][n].term = log[j][n].term)
            => SubSeq(log[i], 1, n) = SubSeq(log[j], 1, n)

\* The commit index never points past the end of the log.
CommitIndexBounded ==
    \A i \in Server : commitIndex[i] <= Len(log[i])

\* No two different commands are ever committed at the same index.
CommittedUnique ==
    \A c, d \in committed :
        c.index = d.index => (c.term = d.term /\ c.value = d.value)

\* Servers agree on every index both consider committed.
StateMachineSafety ==
    \A i, j \in Server :
        \A n \in 1..Min(commitIndex[i], commitIndex[j]) :
            log[i][n] = log[j][n]

\* A server that considers an index committed holds the committed command there.
CommittedConsistency ==
    \A c \in committed : \A i \in Server :
        commitIndex[i] >= c.index => HasEntry(i, c)

\* Every committed entry is present on a majority of servers.
CommittedOnQuorum ==
    \A c \in committed : {k \in Server : HasEntry(k, c)} \in Quorum

\* Every leader of a term at or after a commit holds the committed entry.
LeaderCompleteness ==
    \A c \in committed : \A l \in Server :
        (role[l] = Leader /\ currentTerm[l] >= c.cterm) => HasEntry(l, c)

\* No server stores entries from a term later than its current term.
LogTermsBounded ==
    \A i \in Server : \A k \in 1..Len(log[i]) : log[i][k].term <= currentTerm[i]

\* Leadership belongs to a term that a quorum has reached.
LeaderTermQuorum ==
    \A l \in Server :
        role[l] = Leader =>
            {k \in Server : currentTerm[k] >= currentTerm[l]} \in Quorum

Invariants ==
    /\ TypeOK
    /\ ElectionSafety
    /\ LogMatching
    /\ CommitIndexBounded
    /\ CommittedUnique
    /\ StateMachineSafety
    /\ CommittedConsistency
    /\ CommittedOnQuorum
    /\ LeaderCompleteness
    /\ LogTermsBounded
    /\ LeaderTermQuorum

----------------------------------------------------------------------------
(* Action (temporal safety) properties *)

\* Terms never decrease on any server.
TermMonotonic ==
    [][\A i \in Server : currentTerm'[i] >= currentTerm[i]]_vars

\* Commit decisions are never revoked.
CommittedNeverLost ==
    [][committed \subseteq committed']_vars

\* A committed entry already in a server's log is never overwritten or removed.
CommittedNeverOverwritten ==
    [][\A c \in committed : \A i \in Server :
          HasEntry(i, c) => (Len(log'[i]) >= c.index /\ log'[i][c.index] = EntryOf(c))
      ]_vars

----------------------------------------------------------------------------
(* Liveness under partial synchrony *)

\* A stable period: a running leader and a running majority.
StableLeader(l) ==
    /\ up[l]
    /\ role[l] = Leader
    /\ {k \in Server : up[k]} \in Quorum

FullyStable(l) ==
    /\ StableLeader(l)
    /\ \A k \in Server : up[k]

\* If some leader eventually stays stable with a running majority, a leader
\* eventually commits an entry of its own term. The only exception is a
\* leader whose log is already at the model bound.
CommitProgress ==
    (\E l \in Server : <>[]StableLeader(l)) =>
        <>(\E l \in Server :
              /\ role[l] = Leader
              /\ \/ /\ commitIndex[l] > 0
                    /\ commitIndex[l] <= Len(log[l])
                    /\ log[l][commitIndex[l]].term = currentTerm[l]
                 \/ Len(log[l]) = MaxLogLen)

IsCommitted(n, t, v) ==
    \E c \in committed : c.index = n /\ c.term = t /\ c.value = v

ReplicatedEverywhere(n, t, v) ==
    \A i \in Server :
        /\ Len(log[i]) >= n
        /\ log[i][n] = [term |-> t, value |-> v]

\* After a stable period with all servers running, every committed entry
\* eventually appears in every server's log.
EventualReplication ==
    (\E l \in Server : <>[]FullyStable(l)) =>
        \A n \in 1..MaxLogLen, t \in 1..MaxTerm, v \in Value :
            IsCommitted(n, t, v) ~> ReplicatedEverywhere(n, t, v)

THEOREM Spec => []Invariants
THEOREM Spec => TermMonotonic /\ CommittedNeverLost /\ CommittedNeverOverwritten
THEOREM Spec => CommitProgress /\ EventualReplication
=============================================================================
```