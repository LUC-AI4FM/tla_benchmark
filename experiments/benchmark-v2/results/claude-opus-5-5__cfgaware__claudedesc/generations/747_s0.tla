```tla
,
                   LastVotePayload, CurrentLease, CanTakeCheckpoint,
                   IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

NetworkFailure(src, dst) ==
    /\ src /= dst
    /\ NetworkPath[<<src, dst>>]
    /\ NetworkPath' = [NetworkPath EXCEPT ![<<src, dst>>] = FALSE]
    /\ UNCHANGED <<IsNodeUp, CurrentLeader, ReplicatedLog, ExecutionCounter,
                   LastVotePayload, CurrentLease, CanTakeCheckpoint,
                   IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

NetworkRecovery(src, dst) ==
    /\ src /= dst
    /\ ~NetworkPath[<<src, dst>>]
    /\ NetworkPath' = [NetworkPath EXCEPT ![<<src, dst>>] = TRUE]
    /\ UNCHANGED <<IsNodeUp, CurrentLeader, ReplicatedLog, ExecutionCounter,
                   LastVotePayload, CurrentLease, CanTakeCheckpoint,
                   IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

-------------------------------------------------------------------------------------
\* Protocol actions

\* A node becomes leader with votes from a quorum, requiring up-to-date state
ElectLeader(n) ==
    /\ IsNodeUp[n]
    /\ n /= CurrentLeader
    /\ \/ CurrentLeader = NoNode
       \/ ~NetworkPath[<<CurrentLeader, n>>]
    /\ \A m \in Node : LogLen(ReplicatedLog[m]) <= LogLen(ReplicatedLog[n])
    /\ \E Q \in SUBSET Node :
          /\ n \in Q
          /\ Cardinality(Q) >= MajorityNodeCount
          /\ \A m \in Q : IsNodeUp[m] /\ Connected(m, n) /\ Connected(n, m)
          /\ LastVotePayload' =
                [m \in Node |->
                    IF m \in Q
                    THEN [candidate |-> n,
                          logLength |-> LogLen(ReplicatedLog[m])]
                    ELSE LastVotePayload[m]]
    /\ CurrentLeader' = n
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   CurrentLease, TimeoutCounter, LatestCheckpoint>>

\* The leader appends a request assigning a checkpoint lease to a non-leader
SendReplicatedRequest(target) ==
    /\ CurrentLeader /= NoNode
    /\ IsNodeUp[CurrentLeader]
    /\ target /= CurrentLeader
    /\ LET log == ReplicatedLog[CurrentLeader]
           i   == LogLen(log) + 1
       IN /\ i \in LogIndex
          /\ ShouldReplaceLease(LatestLease(log))
          /\ ReplicatedLog' =
                [ReplicatedLog EXCEPT ![CurrentLeader][i] =
                    [node |-> target, expiry |-> TimeoutCounter]]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ExecutionCounter,
                   LastVotePayload, CurrentLease, CanTakeCheckpoint,
                   IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

\* A log entry is copied from one node to another over a working link
PropagateLogEntry(src, dst) ==
    /\ src /= dst
    /\ IsNodeUp[src]
    /\ IsNodeUp[dst]
    /\ NetworkPath[<<src, dst>>]
    /\ LET i == LogLen(ReplicatedLog[dst]) + 1
       IN /\ i \in LogIndex
          /\ ReplicatedLog[src][i] /= NoCheckpointLease
          /\ ReplicatedLog' =
                [ReplicatedLog EXCEPT ![dst][i] = ReplicatedLog[src][i]]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ExecutionCounter,
                   LastVotePayload, CurrentLease, CanTakeCheckpoint,
                   IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

\* A node executes the next committed log entry, updating lease info
ProcessReplicatedRequest(n) ==
    /\ IsNodeUp[n]
    /\ LET i == ExecutionCounter[n] + 1
       IN /\ i \in LogIndex
          /\ ReplicatedLog[n][i] /= NoCheckpointLease
          /\ IsCommitted(i)
          /\ LET lease    == ReplicatedLog[n][i]
                 eligible == IsValidLeaseFor(lease, n) /\ n /= CurrentLeader
             IN /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = i]
                /\ CurrentLease' = [CurrentLease EXCEPT ![n] = lease]
                /\ CanTakeCheckpoint' =
                      [CanTakeCheckpoint EXCEPT ![n] = eligible]
                /\ IsTakingCheckpoint' =
                      [IsTakingCheckpoint EXCEPT ![n] =
                          IsTakingCheckpoint[n] /\ eligible]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ReplicatedLog,
                   LastVotePayload, TimeoutCounter, LatestCheckpoint>>

StartCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ CanTakeCheckpoint[n]
    /\ ~IsTakingCheckpoint[n]
    /\ n /= CurrentLeader
    /\ IsValidLeaseFor(CurrentLease[n], n)
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ReplicatedLog,
                   ExecutionCounter, LastVotePayload, CurrentLease,
                   CanTakeCheckpoint, TimeoutCounter, LatestCheckpoint>>

FinishCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ IsTakingCheckpoint[n]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
    /\ LatestCheckpoint' = [node |-> n, index |-> ExecutionCounter[n]]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ReplicatedLog,
                   ExecutionCounter, LastVotePayload, CurrentLease,
                   TimeoutCounter>>

\* A timeout invalidates all outstanding leases
TriggerTimeout ==
    /\ TimeoutCounter < MaxTimeout
    /\ TimeoutCounter' = TimeoutCounter + 1
    /\ CanTakeCheckpoint' = [n \in Node |-> FALSE]
    /\ IsTakingCheckpoint' = [n \in Node |-> FALSE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, CurrentLeader, ReplicatedLog,
                   ExecutionCounter, LastVotePayload, CurrentLease,
                   LatestCheckpoint>>

-------------------------------------------------------------------------------------
Next ==
    \/ \E n \in Node : NodeFailure(n)
    \/ \E n \in Node : NodeRecovery(n)
    \/ \E s, d \in Node : NetworkFailure(s, d)
    \/ \E s, d \in Node : NetworkRecovery(s, d)
    \/ \E n \in Node : ElectLeader(n)
    \/ \E n \in Node : SendReplicatedRequest(n)
    \/ \E s, d \in Node : PropagateLogEntry(s, d)
    \/ \E n \in Node : ProcessReplicatedRequest(n)
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : FinishCheckpoint(n)
    \/ TriggerTimeout

Fairness ==
    /\ \A n \in Node : WF_vars(NodeRecovery(n))
    /\ \A s, d \in Node : WF_vars(NetworkRecovery(s, d))
    /\ \A n \in Node : SF_vars(ElectLeader(n))
    /\ \A n \in Node : SF_vars(SendReplicatedRequest(n))
    /\ \A s, d \in Node : SF_vars(PropagateLogEntry(s, d))
    /\ \A n \in Node : SF_vars(ProcessReplicatedRequest(n))
    /\ \A n \in Node : SF_vars(StartCheckpoint(n))
    /\ \A n \in Node : SF_vars(FinishCheckpoint(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------------
SafetyInvariant ==
    \* At most one node takes a checkpoint at a time
    /\ \A m, n \in Node :
          (IsTakingCheckpoint[m] /\ IsTakingCheckpoint[n]) => m = n
    \* Only non-leaders holding a valid, non-timed-out lease may checkpoint
    /\ \A n \in Node :
          IsTakingCheckpoint[n] =>
              /\ n /= CurrentLeader
              /\ IsValidLeaseFor(CurrentLease[n], n)
    \* Replicated logs never conflict
    /\ \A m, n \in Node : \A i \in LogIndex :
          (/\ ReplicatedLog[m][i] /= NoCheckpointLease
           /\ ReplicatedLog[n][i] /= NoCheckpointLease)
              => ReplicatedLog[m][i] = ReplicatedLog[n][i]

TemporalInvariant ==
    /\ <>(\E n \in Node : CanTakeCheckpoint[n])
    /\ \A n \in Node :
          CanTakeCheckpoint[n] ~> (IsTakingCheckpoint[n] \/ ~CanTakeCheckpoint[n])
    /\ <>(LatestCheckpoint.node /= NoNode)

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant)
=====================================================================================
```