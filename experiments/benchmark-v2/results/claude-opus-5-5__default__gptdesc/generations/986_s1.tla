EAN]
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

\* Every node's local view consists of real graph edges.
\* No edge is both incoming and outgoing.
EdgesInGraph ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

\* Pruned nodes have no remaining edges.
PrunedIsolated ==
  \A n \in Nodes :
     ~active[n] => (incoming[n] = {} /\ outgoing[n] = {})

\* Two nodes that are both at the start of a round agree on their edges.
EdgeConsistency ==
  \A n, m \in Nodes :
     (phase[n] = "down" /\ phase[m] = "down") =>
        (m \in outgoing[n] <=> n \in incoming[m])

\* The smallest node is never pruned and always remains a source.
LeaderSurvives ==
  /\ active[Leader]
  /\ incoming[Leader] = {}

Inv ==
  /\ TypeOK
  /\ EdgesInGraph
  /\ PrunedIsolated
  /\ EdgeConsistency
  /\ LeaderSurvives

-----------------------------------------------------------------------------
(* Termination *)

\* Only the leader is active, it is isolated, and no messages are pending.
Terminated ==
  /\ \A n \in Nodes : active[n] <=> (n = Leader)
  /\ incoming[Leader] = {}
  /\ outgoing[Leader] = {}
  /\ \A n \in Nodes : mailbox[n] = {}

Termination == <>Terminated

StableTermination == [](Terminated => []Terminated)

\* The system is deadlocked exactly when it has terminated.
DeadlockIffTerminated == [](~ENABLED Next <=> Terminated)

=============================================================================
```