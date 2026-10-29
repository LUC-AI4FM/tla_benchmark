---------------------------- MODULE CheckpointCoordination ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node

ASSUME Node # {}

NoNode == CHOOSE n : n \notin Node

LogIndex == 1 .. 3

TimeoutLimit == 2

CheckpointLease == [node : Node, index : LogIndex]

NoCheckpointLease == [node |-> NoNode, index |-> 0]

LogEntry == CheckpointLease \cup {NoCheckpointLease}

Quorums == {Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node)}

VARIABLES
  isNodeUp,
  networkPath,
  leader,
  log,
  timer,
  isTakingCheckpoint,
  lastCompleted,
  leaderCompletion,
  latestCheckpoint

vars == <<isNodeUp, networkPath, leader, log, timer, isTakingCheckpoint,
          lastCompleted, leaderCompletion, latestCheckpoint>>

-----------------------------------------------------------------------------
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Connected(a, b) == a = b \/ networkPath[<<a, b>>]

FilledIndices(n) == {i \in LogIndex : log[n][i] # NoCheckpointLease}

LogLength(n) == Cardinality(FilledIndices(n))

OpenIndices == {i \in LogIndex : \A n \in Node : log[n][i] = NoCheckpointLease}

AllFilled == {i \in LogIndex : \E n \in Node : log[n][i] # NoCheckpointLease}

LatestLease(n) ==
  IF FilledIndices(n) = {} THEN NoCheckpointLease
  ELSE log[n][Max(FilledIndices(n))]

IsExpired(lease) == timer[lease.index] >= TimeoutLimit

LeaderLease ==
  IF leader = NoNode THEN NoCheckpointLease
  ELSE LET l == LatestLease(leader) IN
         IF l = NoCheckpointLease THEN NoCheckpointLease
         ELSE IF IsExpired(l) THEN NoCheckpointLease
         ELSE l

CanTakeCheckpoint(n) ==
  /\ isNodeUp[n]
  /\ LatestLease(n) # NoCheckpointLease
  /\ LatestLease(n).node = n
  /\ ~IsExpired(LatestLease(n))
  /\ lastCompleted[n] # LatestLease(n)

ShouldReplaceLease ==
  LET cur == LatestLease(leader) IN
    \/ cur = NoCheckpointLease
    \/ IsExpired(cur)
    \/ leaderCompletion = cur

HasQuorumConnectivity(n) ==
  \E Q \in Quorums :
    /\ n \in Q
    /\ \A m \in Q : isNodeUp[m] /\ Connected(n, m) /\ Connected(m, n)

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ isNodeUp \in [Node -> BOOLEAN]
  /\ networkPath \in [Node \X Node -> BOOLEAN]
  /\ leader \in Node \cup {NoNode}
  /\ log \in [Node -> [LogIndex -> LogEntry]]
  /\ timer \in [LogIndex -> 0 .. TimeoutLimit]
  /\ isTakingCheckpoint \in [Node -> BOOLEAN]
  /\ lastCompleted \in [Node -> LogEntry]
  /\ leaderCompletion \in LogEntry
  /\ latestCheckpoint \in [LogIndex -> LogEntry]

Init ==
  /\ isNodeUp = [n \in Node |-> TRUE]
  /\ networkPath = [p \in Node \X Node |-> TRUE]
  /\ leader = NoNode
  /\ log = [n \in Node |-> [i \in LogIndex |-> NoCheckpointLease]]
  /\ timer = [i \in LogIndex |-> 0]
  /\ isTakingCheckpoint = [n \in Node |-> FALSE]
  /\ lastCompleted = [n \in Node |-> NoCheckpointLease]
  /\ leaderCompletion = NoCheckpointLease
  /\ latestCheckpoint = [i \in LogIndex |-> NoCheckpointLease]

-----------------------------------------------------------------------------
NodeFail(n) ==
  /\ isNodeUp[n]
  /\ isNodeUp' = [isNodeUp EXCEPT ![n] = FALSE]
  /\ isTakingCheckpoint' = [isTakingCheckpoint EXCEPT ![n] = FALSE]
  /\ IF leader = n
       THEN /\ leader' = NoNode
            /\ leaderCompletion' = NoCheckpointLease
       ELSE UNCHANGED <<leader, leaderCompletion>>
  /\ UNCHANGED <<networkPath, log, timer, lastCompleted, latestCheckpoint>>

NodeRecover(n) ==
  /\ ~isNodeUp[n]
  /\ isNodeUp' = [isNodeUp EXCEPT ![n] = TRUE]
  /\ log' = [log EXCEPT ![n] =
              [i \in LogIndex |->
                 IF log[n][i] # NoCheckpointLease THEN log[n][i]
                 ELSE latestCheckpoint[i]]]
  /\ UNCHANGED <<networkPath, leader, timer, isTakingCheckpoint,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

LinkFail(a, b) ==
  /\ a # b
  /\ networkPath[<<a, b>>]
  /\ networkPath' = [networkPath EXCEPT ![<<a, b>>] = FALSE]
  /\ UNCHANGED <<isNodeUp, leader, log, timer, isTakingCheckpoint,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

LinkRecover(a, b) ==
  /\ a # b
  /\ ~networkPath[<<a, b>>]
  /\ networkPath' = [networkPath EXCEPT ![<<a, b>>] = TRUE]
  /\ UNCHANGED <<isNodeUp, leader, log, timer, isTakingCheckpoint,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

BecomeLeader(n) ==
  /\ leader = NoNode
  /\ isNodeUp[n]
  /\ HasQuorumConnectivity(n)
  /\ \A m \in Node : LogLength(m) <= LogLength(n)
  /\ ~CanTakeCheckpoint(n)
  /\ ~isTakingCheckpoint[n]
  /\ leader' = n
  /\ leaderCompletion' = NoCheckpointLease
  /\ UNCHANGED <<isNodeUp, networkPath, log, timer, isTakingCheckpoint,
                 lastCompleted, latestCheckpoint>>

LeaderStepDown ==
  /\ leader # NoNode
  /\ ~HasQuorumConnectivity(leader)
  /\ leader' = NoNode
  /\ leaderCompletion' = NoCheckpointLease
  /\ UNCHANGED <<isNodeUp, networkPath, log, timer, isTakingCheckpoint,
                 lastCompleted, latestCheckpoint>>

GrantLease(f) ==
  /\ leader # NoNode
  /\ isNodeUp[leader]
  /\ f \in Node \ {leader}
  /\ ShouldReplaceLease
  /\ LogLength(leader) + 1 \in LogIndex
  /\ LET i   == LogLength(leader) + 1
         old == LatestLease(leader)
         new == [node |-> f, index |-> i]
     IN /\ log' = [log EXCEPT ![leader][i] = new]
        /\ timer' = IF old = NoCheckpointLease
                      THEN [timer EXCEPT ![i] = 0]
                      ELSE [timer EXCEPT ![i] = 0, ![old.index] = TimeoutLimit]
  /\ leaderCompletion' = NoCheckpointLease
  /\ UNCHANGED <<isNodeUp, networkPath, leader, isTakingCheckpoint,
                 lastCompleted, latestCheckpoint>>

Replicate(f) ==
  /\ leader # NoNode
  /\ isNodeUp[leader]
  /\ f # leader
  /\ isNodeUp[f]
  /\ Connected(leader, f)
  /\ LogLength(f) < LogLength(leader)
  /\ LET i == LogLength(f) + 1 IN
       log' = [log EXCEPT ![f][i] = log[leader][i]]
  /\ UNCHANGED <<isNodeUp, networkPath, leader, timer, isTakingCheckpoint,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

StartCheckpoint(n) ==
  /\ CanTakeCheckpoint(n)
  /\ ~isTakingCheckpoint[n]
  /\ isTakingCheckpoint' = [isTakingCheckpoint EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<isNodeUp, networkPath, leader, log, timer,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

FinishCheckpoint(n) ==
  /\ isNodeUp[n]
  /\ isTakingCheckpoint[n]
  /\ isTakingCheckpoint' = [isTakingCheckpoint EXCEPT ![n] = FALSE]
  /\ lastCompleted' = [lastCompleted EXCEPT ![n] = LatestLease(n)]
  /\ latestCheckpoint' = log[n]
  /\ UNCHANGED <<isNodeUp, networkPath, leader, log, timer, leaderCompletion>>

ReportCompletion(n) ==
  /\ isNodeUp[n]
  /\ leader # NoNode
  /\ isNodeUp[leader]
  /\ lastCompleted[n] # NoCheckpointLease
  /\ Connected(n, leader)
  /\ leaderCompletion # lastCompleted[n]
  /\ leaderCompletion' = lastCompleted[n]
  /\ UNCHANGED <<isNodeUp, networkPath, leader, log, timer,
                 isTakingCheckpoint, lastCompleted, latestCheckpoint>>

Tick ==
  /\ AllFilled # {}
  /\ LET i == Max(AllFilled)
         holder == (CHOOSE e \in {log[m][i] : m \in Node} :
                       e # NoCheckpointLease).node
     IN /\ timer[i] < TimeoutLimit
        /\ timer' = [timer EXCEPT ![i] = timer[i] + 1]
        /\ isTakingCheckpoint' =
             IF timer[i] + 1 >= TimeoutLimit
               THEN [isTakingCheckpoint EXCEPT ![holder] = FALSE]
               ELSE isTakingCheckpoint
  /\ UNCHANGED <<isNodeUp, networkPath, leader, log,
                 lastCompleted, leaderCompletion, latestCheckpoint>>

Next ==
  \/ \E n \in Node :
       \/ NodeFail(n)
       \/ NodeRecover(n)
       \/ BecomeLeader(n)
       \/ GrantLease(n)
       \/ Replicate(n)
       \/ StartCheckpoint(n)
       \/ FinishCheckpoint(n)
       \/ ReportCompletion(n)
  \/ \E a, b \in Node : LinkFail(a, b) \/ LinkRecover(a, b)
  \/ LeaderStepDown
  \/ Tick

Fairness ==
  /\ \A n \in Node :
       /\ WF_vars(NodeRecover(n))
       /\ WF_vars(BecomeLeader(n))
       /\ WF_vars(GrantLease(n))
       /\ WF_vars(Replicate(n))
       /\ WF_vars(StartCheckpoint(n))
       /\ WF_vars(FinishCheckpoint(n))
       /\ WF_vars(ReportCompletion(n))
  /\ \A a, b \in Node : WF_vars(LinkRecover(a, b))
  /\ WF_vars(LeaderStepDown)
  /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

AtMostOneCanCheckpoint ==
  \A a, b \in Node : CanTakeCheckpoint(a) /\ CanTakeCheckpoint(b) => a = b

AtMostOneTakingCheckpoint ==
  \A a, b \in Node : isTakingCheckpoint[a] /\ isTakingCheckpoint[b] => a = b

LeaderNeverCheckpoints ==
  leader # NoNode => (~isTakingCheckpoint[leader] /\ ~CanTakeCheckpoint(leader))

LeaseConsistency ==
  leader # NoNode =>
    IF LeaderLease = NoCheckpointLease
      THEN \A n \in Node : ~CanTakeCheckpoint(n)
      ELSE \A n \in Node : CanTakeCheckpoint(n) => n = LeaderLease.node

ValidAuthorization ==
  \A n \in Node : isTakingCheckpoint[n] => CanTakeCheckpoint(n)

LogConsistency ==
  \A a, b \in Node : \A i \in LogIndex :
    (log[a][i] # NoCheckpointLease /\ log[b][i] # NoCheckpointLease)
      => log[a][i] = log[b][i]

SafetyInvariant ==
  /\ AtMostOneCanCheckpoint
  /\ AtMostOneTakingCheckpoint
  /\ LeaderNeverCheckpoints
  /\ LeaseConsistency
  /\ ValidAuthorization
  /\ LogConsistency

\* Liveness

EventuallyCanCheckpoint == <>(\E n \in Node : CanTakeCheckpoint(n))

CheckpointInitiation ==
  \A n \in Node :
    CanTakeCheckpoint(n) ~>
      (isTakingCheckpoint[n] \/ ~isNodeUp[n] \/ ~CanTakeCheckpoint(n))

CheckpointCompletion ==
  \A n \in Node :
    isTakingCheckpoint[n] ~>
      (~isTakingCheckpoint[n])

EventuallyCheckpointCompleted ==
  <>(\E i \in LogIndex : latestCheckpoint[i] # NoCheckpointLease
       \/ \E n \in Node : lastCompleted[n] # NoCheckpointLease)

=============================================================================