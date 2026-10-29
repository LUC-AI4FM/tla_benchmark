------------------------- MODULE MCCheckpointCoordination -------------------------
EXTENDS Naturals, FiniteSets, TLC

----------------------------- MODULE CheckpointCoordination -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node, NoNode, LogIndex, LeaseDuration

VARIABLES leader, lastClosed, clock, lease, checkpointing, checkpointIndex

vars == <<leader, lastClosed, clock, lease, checkpointing, checkpointIndex>>

TypeOK ==
  /\ leader \in Node
  /\ lastClosed \in LogIndex
  /\ clock \in Nat
  /\ lease \in [node : Node \cup {NoNode}, expiration : Nat]
  /\ checkpointing \subseteq Node
  /\ checkpointIndex \in LogIndex

IsOpen(i) == i \in LogIndex /\ i > lastClosed

LeaseValid == lease.node # NoNode /\ clock < lease.expiration

CanReplaceLease(n) == ~LeaseValid

Init ==
  /\ leader \in Node
  /\ lastClosed = 0
  /\ clock = 0
  /\ lease = [node |-> NoNode, expiration |-> 0]
  /\ checkpointing = {}
  /\ checkpointIndex = 0

ElectLeader(n) ==
  /\ n # leader
  /\ leader' = n
  /\ UNCHANGED <<lastClosed, clock, lease, checkpointing, checkpointIndex>>

CloseIndex ==
  /\ lastClosed + 1 \in LogIndex
  /\ lastClosed' = lastClosed + 1
  /\ UNCHANGED <<leader, clock, lease, checkpointing, checkpointIndex>>

Tick ==
  /\ clock' = clock + 1
  /\ checkpointing' = IF clock + 1 >= lease.expiration THEN {} ELSE checkpointing
  /\ UNCHANGED <<leader, lastClosed, lease, checkpointIndex>>

AcquireLease(n, P(_)) ==
  /\ P(n)
  /\ lease' = [node |-> n, expiration |-> clock + LeaseDuration]
  /\ UNCHANGED <<leader, lastClosed, clock, checkpointing, checkpointIndex>>

StartCheckpoint(n) ==
  /\ LeaseValid
  /\ lease.node = n
  /\ n \notin checkpointing
  /\ checkpointing' = checkpointing \cup {n}
  /\ UNCHANGED <<leader, lastClosed, clock, lease, checkpointIndex>>

FinishCheckpoint(n) ==
  /\ n \in checkpointing
  /\ LeaseValid
  /\ lease.node = n
  /\ checkpointIndex' = lastClosed
  /\ checkpointing' = checkpointing \ {n}
  /\ UNCHANGED <<leader, lastClosed, clock, lease>>

AbortCheckpoint(n) ==
  /\ n \in checkpointing
  /\ lease.node # n
  /\ checkpointing' = checkpointing \ {n}
  /\ UNCHANGED <<leader, lastClosed, clock, lease, checkpointIndex>>

NextWith(P(_)) ==
  \/ \E n \in Node : ElectLeader(n)
  \/ CloseIndex
  \/ Tick
  \/ \E n \in Node : AcquireLease(n, P)
  \/ \E n \in Node : StartCheckpoint(n)
  \/ \E n \in Node : FinishCheckpoint(n)
  \/ \E n \in Node : AbortCheckpoint(n)

Next == NextWith(CanReplaceLease)

Spec == Init /\ [][Next]_vars

AtMostOneCheckpointer == Cardinality(checkpointing) <= 1
=========================================================================================