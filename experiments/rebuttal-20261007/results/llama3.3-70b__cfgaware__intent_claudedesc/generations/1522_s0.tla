---------------------------- MODULE HuangTerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, Leader
VARIABLES localWeight, messageQueues, activeProcesses

Init ==
  /\ localWeight = [p \in Processes |-> IF p = Leader THEN 1 ELSE 0]
  /\ messageQueues = [p \in Processes |-> {}]
  /\ activeProcesses = {Leader}

TypeInvariant ==
  /\ localWeight \in [Processes -> (0 .. 1)]
  /\ messageQueues \in [Processes -> SUBSET (Processes \X (0 .. 1))]
  /\ activeProcesses \subseteq Processes

Send(p, q) ==
  /\ p \in activeProcesses
  /\ q \in Processes
  /\ localWeight[p] > 0
  /\ localWeight' = [localWeight EXCEPT ![p] = @ / 2]
  /\ messageQueues' = [messageQueues EXCEPT ![q] = @ \cup {(p, @ / 2)}]
  /\ activeProcesses' = activeProcesses

Receive(p) ==
  /\ ~ (p = Leader)
  /\ messageQueues[p] # {}
  /\ \E q \in Processes, w \in (0 .. 1) : (q, w) \in messageQueues[p]
  /\ localWeight' = [localWeight EXCEPT ![p] = @ + w]
  /\ messageQueues' = [messageQueues EXCEPT ![p] = @ \ {(q, w)}]
  /\ activeProcesses' = activeProcesses \cup {p}

Return(p) ==
  /\ ~ (p = Leader)
  /\ localWeight[p] > 0
  /\ localWeight' = [localWeight EXCEPT ![p] = 0]
  /\ messageQueues' = [messageQueues EXCEPT ![Leader] = @ \cup {(p, @)}]
  /\ activeProcesses' = activeProcesses \ {p}

LeaderIdle ==
  /\ Leader \in activeProcesses
  /\ localWeight[Leader] = 1
  /\ messageQueues[Leader] = {}
  /\ activeProcesses' = activeProcesses \ {Leader}
  /\ localWeight' = localWeight
  /\ messageQueues' = messageQueues

LeaderReceive ==
  /\ Leader \in activeProcesses
  /\ messageQueues[Leader] # {}
  /\ \E q \in Processes, w \in (0 .. 1) : (q, w) \in messageQueues[Leader]
  /\ localWeight' = [localWeight EXCEPT ![Leader] = @ + w]
  /\ messageQueues' = [messageQueues EXCEPT ![Leader] = @ \ {(q, w)}]
  /\ activeProcesses' = activeProcesses

Next ==
  \/ \E p, q \in Processes : Send(p, q)
  \/ \E p \in Processes : Receive(p)
  \/ \E p \in Processes : Return(p)
  \/ LeaderIdle
  \/ LeaderReceive

Spec == Init /\ [][Next]_<<localWeight, messageQueues, activeProcesses>>
=============================================================================