---------------------------- MODULE AbstractRaftRSM ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Servers,      \* the fixed set of servers
          Terms,        \* the (bounded) set of terms
          StartTerm,    \* initial term of every server
          NodeOne, NodeTwo, NodeThree

VARIABLES currentTerm,  \* currentTerm[s]: latest term known to s
          state,        \* state[s] \in {Leader, Follower}
          log,          \* log[s]: sequence of entry terms (entry = <<index, term>>)
          committed     \* set of committed entries [entry |-> <<idx,term>>, term |-> t]

vars == <<currentTerm, state, log, committed>>

Leader   == "Leader"
Follower == "Follower"

MaxLogLen == 3

-----------------------------------------------------------------------------
(* Helpers *)

Quorums == {Q \in SUBSET Servers : Cardinality(Q) * 2 > Cardinality(Servers)}

LastTerm(xlog) == IF Len(xlog) = 0 THEN StartTerm ELSE xlog[Len(xlog)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* log a is at least as up to date as log b
UpToDate(a, b) ==
    \/ LastTerm(a) > LastTerm(b)
    \/ (LastTerm(a) = LastTerm(b) /\ Len(a) >= Len(b))

InLog(e, s) == e[1] \in DOMAIN log[s] /\ log[s][e[1]] = e[2]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ currentTerm = [s \in Servers |-> StartTerm]
    /\ state       = [s \in Servers |-> Follower]
    /\ log         = [s \in Servers |-> <<>>]
    /\ committed   = {}

-----------------------------------------------------------------------------
(* Actions *)

\* A leader receives a client command and appends it to its local log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Follower j accepts the next entry from i (append request succeeds only
\* when the previous entry matches). Messages may be lost/reordered: this
\* step simply may or may not occur.
GetEntries(i, j) ==
    /\ i /= j
    /\ state[j] = Follower
    /\ currentTerm[j] <= currentTerm[i]
    /\ Len(log[i]) > Len(log[j])
    /\ LET idx == Len(log[j]) + 1 IN
         /\ (idx = 1 \/ log[j][idx - 1] = log[i][idx - 1])
         /\ log' = [log EXCEPT ![j] = Append(log[j], log[i][idx])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Follower j's log diverges from i's newer log: truncate its last entry.
RollbackEntries(i, j) ==
    /\ i /= j
    /\ state[j] = Follower
    /\ Len(log[j]) > 0
    /\ Len(log[i]) > 0
    /\ LastTerm(log[j]) < LastTerm(log[i])
    /\ \/ Len(log[j]) > Len(log[i])
       \/ log[i][Len(log[j])] /= LastTerm(log[j])
    /\ log' = [log EXCEPT ![j] = SubSeq(log[j], 1, Len(log[j]) - 1)]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Server i is elected leader of a new term by a quorum of voters.
BecomeLeader(i, Q) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in Q
    /\ newTerm \in Terms
    /\ \A v \in Q : currentTerm[v] < newTerm /\ UpToDate(log[i], log[v])
    /\ currentTerm' = [s \in Servers |->
                          IF s \in Q THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Servers |->
                    IF s = i THEN Leader
                    ELSE IF s \in Q THEN Follower ELSE state[s]]
    /\ UNCHANGED <<log, committed>>

\* A leader commits the latest entry of its own term once a quorum in its
\* term holds it.
CommitEntry(i, Q) ==
    LET ind == Len(log[i]) IN
    /\ state[i] = Leader
    /\ ind > 0
    /\ log[i][ind] = currentTerm[i]
    /\ \A s \in Q : /\ Len(log[s]) >= ind
                    /\ log[s][ind] = log[i][ind]
                    /\ currentTerm[s] = currentTerm[i]
    /\ committed' = committed \cup
         {[entry |-> <<ind, currentTerm[i]>>, term |-> currentTerm[i]]}
    /\ UNCHANGED <<currentTerm, state, log>>

\* Term propagation: a server learning of a higher term adopts it and steps down.
UpdateTerms(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Follower]
    /\ UNCHANGED <<log, committed>>

\* Crash and recovery: volatile leadership is lost; term and log are durable.
CrashRecover(i) ==
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<currentTerm, log, committed>>

Next ==
    \/ \E i \in Servers : ClientRequest(i)
    \/ \E i, j \in Servers : GetEntries(i, j)
    \/ \E i, j \in Servers : RollbackEntries(i, j)
    \/ \E i \in Servers, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Servers, Q \in Quorums : CommitEntry(i, Q)
    \/ \E i, j \in Servers : UpdateTerms(i, j)
    \/ \E i \in Servers : CrashRecover(i)

AbsSpec == Init /\ [][Next]_vars

\* Liveness under a stable period: fair replication/commit steps.
LiveSpec ==
    /\ AbsSpec
    /\ \A i, j \in Servers : WF_vars(GetEntries(i, j))
    /\ \A i, j \in Servers : WF_vars(UpdateTerms(i, j))
    /\ \A i \in Servers, Q \in Quorums : WF_vars(CommitEntry(i, Q))

EventuallyCommits ==
    (\E i \in Servers : state[i] = Leader /\ Len(log[i]) > 0) ~> (committed /= {})

-----------------------------------------------------------------------------
(* Invariants and properties *)

TypeOK ==
    /\ currentTerm \in [Servers -> Terms]
    /\ state \in [Servers -> {Leader, Follower}]
    /\ log \in [Servers -> Seq(Terms)]
    /\ committed \subseteq [entry : (1..MaxLogLen) \X Terms, term : Terms]

\* No two committed entries occupy the same index with different terms.
NoConflicts ==
    \A c1, c2 \in committed :
        (c1.entry[1] = c2.entry[1]) => (c1.entry = c2.entry)

\* Leader completeness: leaders of later terms contain all committed entries.
LeaderCompleteness ==
    \A c \in committed, s \in Servers :
        (state[s] = Leader /\ currentTerm[s] > c.term) => InLog(c.entry, s)

\* Committed entries are held by a quorum.
CommittedOnQuorum ==
    \A c \in committed : \E Q \in Quorums : \A s \in Q : InLog(c.entry, s)

\* Log matching.
LogMatching ==
    \A s, t \in Servers : \A k \in DOMAIN log[s] :
        (k \in DOMAIN log[t] /\ log[s][k] = log[t][k]) =>
            SubSeq(log[s], 1, k) = SubSeq(log[t], 1, k)

\* At most one leader per term.
OneLeaderPerTerm ==
    \A s, t \in Servers :
        (state[s] = Leader /\ state[t] = Leader /\ currentTerm[s] = currentTerm[t])
            => s = t

\* Committed set only grows; leader logs only grow within a term;
\* terms are monotonic.
AppendOnlyProp ==
    /\ [][\A c \in committed : c \in committed']_vars
    /\ [][\A s \in Servers :
            (state[s] = Leader /\ state'[s] = Leader
              /\ currentTerm[s] = currentTerm'[s])
                => IsPrefix(log[s], log'[s])]_vars
    /\ [][\A s \in Servers : currentTerm'[s] >= currentTerm[s]]_vars

-----------------------------------------------------------------------------
(* Model-checking definitions *)

MCServers   == {NodeOne, NodeTwo, NodeThree}
MCTerms     == 0..3
MCStartTerm == 0

\* Finite replacement for Seq, bounded by the maximum log length.
MCSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLogLen}

MCTypeOK ==
    /\ currentTerm \in [Servers -> Terms]
    /\ state \in [Servers -> {Leader, Follower}]
    /\ log \in [Servers -> MCSeq(Terms)]
    /\ committed \subseteq [entry : (1..MaxLogLen) \X Terms, term : Terms]

Symmetry == Permutations(MCServers)

MaxLogLengthConstraint == \A s \in Servers : Len(log[s]) <= MaxLogLen

=============================================================================