------------------------- MODULE CheckpointCoordination -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,      \* set of nodes in the cluster
          Majority    \* quorum threshold

ASSUME Majority \in Nat /\ Majority > 0 /\ Majority <= Cardinality(Nodes)

None == CHOOSE x : x \notin Nodes

VARIABLES
    nodeUp,            \* [Nodes -> BOOLEAN] node availability
    linkUp,            \* [Nodes \X Nodes -> BOOLEAN] unidirectional connectivity
    leader,            \* current leader or None
    log,               \* [Nodes -> Seq(Request)] replicated log copies
    executed,          \* [Nodes -> Nat] execution progress counters
    votes,             \* [Nodes -> Nodes \cup {None}] vote payloads
    lease,             \* [Nodes -> [holder, epoch]] checkpoint lease knowledge
    checkpointing,     \* [Nodes -> BOOLEAN] checkpoint-taking status
    timeout,           \* global timeout counter (lease epoch)
    latestCheckpoint   \* latest completed checkpoint [node, index]

vars == << nodeUp, linkUp, leader, log, executed, votes, lease,
           checkpointing, timeout, latestCheckpoint >>

Request == [holder : Nodes, epoch : Nat]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Eligible(n) ==
    /\ nodeUp[n]
    /\ leader # n
    /\ lease[n].holder = n
    /\ lease[n].epoch = timeout

TypeOK ==
    /\ nodeUp \in [Nodes -> BOOLEAN]
    /\ linkUp \in [Nodes \X Nodes -> BOOLEAN]
    /\ leader \in Nodes \cup {None}
    /\ \A n \in Nodes : log[n] \in Seq(Request)
    /\ executed \in [Nodes -> Nat]
    /\ votes \in [Nodes -> Nodes \cup {None}]
    /\ lease \in [Nodes -> [holder : Nodes \cup {None}, epoch : Nat]]
    /\ checkpointing \in [Nodes -> BOOLEAN]
    /\ timeout \in Nat
    /\ latestCheckpoint \in [node : Nodes \cup {None}, index : Nat]

Init ==
    /\ nodeUp = [n \in Nodes |-> TRUE]
    /\ linkUp = [p \in Nodes \X Nodes |-> TRUE]
    /\ leader = None
    /\ log = [n \in Nodes |-> << >>]
    /\ executed = [n \in Nodes |-> 0]
    /\ votes = [n \in Nodes |-> None]
    /\ lease = [n \in Nodes |-> [holder |-> None, epoch |-> 0]]
    /\ checkpointing = [n \in Nodes |-> FALSE]
    /\ timeout = 0
    /\ latestCheckpoint = [node |-> None, index |-> 0]

-----------------------------------------------------------------------------
\* Environment actions

NodeFail(n) ==
    /\ nodeUp[n]
    /\ nodeUp' = [nodeUp EXCEPT ![n] = FALSE]
    /\ leader' = IF leader = n THEN None ELSE leader
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED << linkUp, log, executed, votes, lease, timeout, latestCheckpoint >>

NodeRecover(n) ==
    /\ ~nodeUp[n]
    /\ nodeUp' = [nodeUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED << linkUp, leader, log, executed, votes, lease,
                    checkpointing, timeout, latestCheckpoint >>

LinkFail(a, b) ==
    /\ a # b
    /\ linkUp[<<a, b>>]
    /\ linkUp' = [linkUp EXCEPT ![<<a, b>>] = FALSE]
    /\ UNCHANGED << nodeUp, leader, log, executed, votes, lease,
                    checkpointing, timeout, latestCheckpoint >>

LinkRecover(a, b) ==
    /\ a # b
    /\ ~linkUp[<<a, b>>]
    /\ linkUp' = [linkUp EXCEPT ![<<a, b>>] = TRUE]
    /\ UNCHANGED << nodeUp, leader, log, executed, votes, lease,
                    checkpointing, timeout, latestCheckpoint >>

-----------------------------------------------------------------------------
\* Protocol actions

Elect(c) ==
    /\ leader = None
    /\ nodeUp[c]
    /\ ~checkpointing[c]
    /\ \A m \in Nodes : IsPrefix(log[m], log[c])          \* up-to-date
    /\ \E Q \in SUBSET Nodes :
          /\ c \in Q
          /\ Cardinality(Q) >= Majority
          /\ \A q \in Q : nodeUp[q] /\ (q = c \/ linkUp[<<q, c>>])
          /\ votes' = [n \in Nodes |-> IF n \in Q THEN c ELSE votes[n]]
    /\ leader' = c
    /\ UNCHANGED << nodeUp, linkUp, log, executed, lease,
                    checkpointing, timeout, latestCheckpoint >>

SendReplicatedRequest(l, n) ==
    /\ leader = l
    /\ nodeUp[l]
    /\ n # l
    /\ \A i \in 1..Len(log[l]) : log[l][i].epoch # timeout   \* one lease per epoch
    /\ log' = [log EXCEPT ![l] = Append(log[l], [holder |-> n, epoch |-> timeout])]
    /\ UNCHANGED << nodeUp, linkUp, leader, executed, votes, lease,
                    checkpointing, timeout, latestCheckpoint >>

Propagate(from, to) ==
    /\ from # to
    /\ nodeUp[from] /\ nodeUp[to]
    /\ linkUp[<<from, to>>]
    /\ Len(log[from]) > Len(log[to])
    /\ IsPrefix(log[to], log[from])
    /\ log' = [log EXCEPT ![to] = log[from]]
    /\ UNCHANGED << nodeUp, linkUp, leader, executed, votes, lease,
                    checkpointing, timeout, latestCheckpoint >>

ProcessRequest(n) ==
    /\ nodeUp[n]
    /\ executed[n] < Len(log[n])
    /\ LET req == log[n][executed[n] + 1] IN
         lease' = [lease EXCEPT ![n] = [holder |-> req.holder, epoch |-> req.epoch]]
    /\ executed' = [executed EXCEPT ![n] = executed[n] + 1]
    /\ UNCHANGED << nodeUp, linkUp, leader, log, votes,
                    checkpointing, timeout, latestCheckpoint >>

StartCheckpoint(n) ==
    /\ ~checkpointing[n]
    /\ Eligible(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED << nodeUp, linkUp, leader, log, executed, votes, lease,
                    timeout, latestCheckpoint >>

FinishCheckpoint(n) ==
    /\ nodeUp[n]
    /\ checkpointing[n]
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ latestCheckpoint' = [node |-> n, index |-> executed[n]]
    /\ lease' = [lease EXCEPT ![n] = [holder |-> None, epoch |-> lease[n].epoch]]
    /\ UNCHANGED << nodeUp, linkUp, leader, log, executed, votes, timeout >>

Timeout ==
    /\ timeout' = timeout + 1
    /\ checkpointing' = [n \in Nodes |-> FALSE]   \* old leases invalidated
    /\ UNCHANGED << nodeUp, linkUp, leader, log, executed, votes, lease,
                    latestCheckpoint >>

-----------------------------------------------------------------------------

Next ==
    \/ \E n \in Nodes : NodeFail(n) \/ NodeRecover(n)
    \/ \E a, b \in Nodes : LinkFail(a, b) \/ LinkRecover(a, b)
    \/ \E c \in Nodes : Elect(c)
    \/ \E l, n \in Nodes : SendReplicatedRequest(l, n)
    \/ \E a, b \in Nodes : Propagate(a, b)
    \/ \E n \in Nodes : ProcessRequest(n)
    \/ \E n \in Nodes : StartCheckpoint(n)
    \/ \E n \in Nodes : FinishCheckpoint(n)
    \/ Timeout

Fairness ==
    /\ \A n \in Nodes : WF_vars(NodeRecover(n))
    /\ \A a, b \in Nodes : WF_vars(LinkRecover(a, b))
    /\ \A c \in Nodes : SF_vars(Elect(c))
    /\ \A l, n \in Nodes : SF_vars(SendReplicatedRequest(l, n))
    /\ \A a, b \in Nodes : SF_vars(Propagate(a, b))
    /\ \A n \in Nodes : SF_vars(ProcessRequest(n))
    /\ \A n \in Nodes : SF_vars(StartCheckpoint(n))
    /\ \A n \in Nodes : SF_vars(FinishCheckpoint(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

MutualExclusion ==
    \A a, b \in Nodes : (checkpointing[a] /\ checkpointing[b]) => a = b

OnlyValidLeaseHolders ==
    \A n \in Nodes : checkpointing[n] =>
        /\ n # leader
        /\ lease[n].holder = n
        /\ lease[n].epoch = timeout

LogsNoConflict ==
    \A a, b \in Nodes : IsPrefix(log[a], log[b]) \/ IsPrefix(log[b], log[a])

Safety == MutualExclusion /\ OnlyValidLeaseHolders /\ LogsNoConflict

\* Liveness

EventuallyEligible == <>(\E n \in Nodes : Eligible(n))

EligibleProgress ==
    \A n \in Nodes : Eligible(n) ~> (checkpointing[n] \/ ~Eligible(n))

EventuallyCheckpointCompletes == <>(latestCheckpoint.node # None)

TemporalInvariant ==
    EventuallyEligible /\ EligibleProgress /\ EventuallyCheckpointCompletes

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => TemporalInvariant
=============================================================================