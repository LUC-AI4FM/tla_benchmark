---------------------------- MODULE CheckpointLeaseCoordination ----------------------------
(***************************************************************************)
(* Checkpoint coordination for a replicated state machine with leader     *)
(* lease ownership.                                                        *)
(*                                                                         *)
(*  - A shared lease record (holder, epoch, expiry) authorizes progress.   *)
(*  - Each node keeps a local view of its lease (leaseEnd, leaseEpoch).    *)
(*    It considers itself leader while clock < leaseEnd[n].               *)
(*  - The leader appends and commits log entries, proposes a checkpoint    *)
(*    index, and collects acknowledgements. A replica acknowledges by      *)
(*    taking a durable local snapshot at that index.                       *)
(*  - The leader finalizes the checkpoint only after every member, which   *)
(*    means every active or potentially active replica, has acknowledged.  *)
(*    Only then may the log prefix be truncated.                           *)
(*  - On a leader change, the new lease holder takes over the pending      *)
(*    proposal under its own epoch. Acks from older epochs are discarded.  *)
(*  - Crashed replicas restart from their own durable snapshot. Any        *)
(*    replica is therefore potentially active and may need log entries    *)
(*    above its snapshot.                                                  *)
(*                                                                         *)
(* Timing model: the model uses a single global clock with zero drift.     *)
(* Under these timing semantics, lease overlap is never permitted.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,          \* set of replica identities (the full membership)
    Nil,            \* "no holder" marker
    MaxIndex,       \* bound on log length (for model checking)
    LeaseDuration,  \* validity period of a lease grant / renewal
    MaxTime,        \* bound on the global clock
    MaxEpoch,       \* bound on the number of lease acquisitions
    MaxCrashes      \* bound on the number of crash/restart events

ASSUME /\ Nil \notin Nodes
       /\ Nodes /= {}
       /\ MaxIndex \in Nat \ {0}
       /\ LeaseDuration \in Nat \ {0}
       /\ MaxTime \in Nat
       /\ MaxEpoch \in Nat
       /\ MaxCrashes \in Nat

VARIABLES
    clock,          \* global time
    lease,          \* shared lease record [holder, epoch, expiry]
    leaseEnd,       \* leaseEnd[n]: time until which n believes it holds the lease
    leaseEpoch,     \* leaseEpoch[n]: epoch of the lease n believes it holds
    logEnd,         \* length of the leader's log (appended entries)
    matchIdx,       \* matchIdx[n]: durable log prefix stored at replica n
    commitIndex,    \* highest committed log index
    applied,        \* applied[n]: highest index applied to n's state machine (volatile)
    snap,           \* snap[n]: index of n's durable local snapshot
    proposalIdx,    \* pending checkpoint proposal index (0 = none)
    proposalEpoch,  \* lease epoch under which the pending proposal is driven
    acks,           \* replicas that acknowledged the pending proposal in proposalEpoch
    msgs,           \* in-flight checkpoint-proposal messages (lossy network)
    checkpointIdx,  \* finalized checkpoint index (safe truncation point)
    truncIdx,       \* index up to which the log has actually been compacted
    crashes         \* number of crash events so far

vars == << clock, lease, leaseEnd, leaseEpoch, logEnd, matchIdx, commitIndex,
           applied, snap, proposalIdx, proposalEpoch, acks, msgs,
           checkpointIdx, truncIdx, crashes >>

leaseVars == << lease, leaseEnd, leaseEpoch >>
logVars   == << logEnd, matchIdx, commitIndex, applied >>
ckptVars  == << snap, proposalIdx, proposalEpoch, acks, msgs, checkpointIdx, truncIdx >>

Indices == 0..MaxIndex
Epochs  == 0..MaxEpoch
MsgType == [idx : 1..MaxIndex, epoch : Epochs, dst : Nodes]

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

\* Node n considers its lease effective.
LeaseEffective(n) == clock < leaseEnd[n]

\* The lease record itself is currently valid.
LeaseValid == lease.holder \in Nodes /\ clock < lease.expiry

\* n is an authorized leader. Its lease is effective, and its epoch is current.
IsLeader(n) == LeaseEffective(n) /\ leaseEpoch[n] = lease.epoch /\ lease.holder = n

Quorum(S) == 2 * Cardinality(S) > Cardinality(Nodes)

---------------------------------------------------------------------------------------------
TypeOK ==
    /\ clock \in 0..MaxTime
    /\ lease \in [holder : Nodes \cup {Nil}, epoch : Epochs, expiry : Nat]
    /\ leaseEnd \in [Nodes -> Nat]
    /\ leaseEpoch \in [Nodes -> Epochs]
    /\ logEnd \in Indices
    /\ matchIdx \in [Nodes -> Indices]
    /\ commitIndex \in Indices
    /\ applied \in [Nodes -> Indices]
    /\ snap \in [Nodes -> Indices]
    /\ proposalIdx \in Indices
    /\ proposalEpoch \in Epochs
    /\ acks \subseteq Nodes
    /\ msgs \subseteq MsgType
    /\ checkpointIdx \in Indices
    /\ truncIdx \in Indices
    /\ crashes \in 0..MaxCrashes

Init ==
    /\ clock = 0
    /\ lease = [holder |-> Nil, epoch |-> 0, expiry |-> 0]
    /\ leaseEnd = [n \in Nodes |-> 0]
    /\ leaseEpoch = [n \in Nodes |-> 0]
    /\ logEnd = 0
    /\ matchIdx = [n \in Nodes |-> 0]
    /\ commitIndex = 0
    /\ applied = [n \in Nodes |-> 0]
    /\ snap = [n \in Nodes |-> 0]
    /\ proposalIdx = 0
    /\ proposalEpoch = 0
    /\ acks = {}
    /\ msgs = {}
    /\ checkpointIdx = 0
    /\ truncIdx = 0
    /\ crashes = 0

---------------------------------------------------------------------------------------------
(* Time *)

Tick ==
    /\ clock < MaxTime
    /\ clock' = clock + 1
    /\ UNCHANGED << leaseVars, logVars, ckptVars, crashes >>

(* Lease management *)

\* A node acquires the lease only once the previous grant has expired.
\* The node then takes over responsibility for any pending checkpoint
\* proposal under the new epoch. Acks from the old epoch are discarded.
AcquireLease(n) ==
    /\ clock >= lease.expiry
    /\ lease.epoch < MaxEpoch
    /\ LET e == lease.epoch + 1
           x == clock + LeaseDuration
       IN /\ lease' = [holder |-> n, epoch |-> e, expiry |-> x]
          /\ leaseEnd' = [leaseEnd EXCEPT ![n] = x]
          /\ leaseEpoch' = [leaseEpoch EXCEPT ![n] = e]
          /\ proposalEpoch' = IF proposalIdx > 0 THEN e ELSE proposalEpoch
          /\ acks' = {}
    /\ UNCHANGED << clock, logVars, snap, proposalIdx, msgs,
                    checkpointIdx, truncIdx, crashes >>

\* The current holder renews its still-valid lease.
RenewLease(n) ==
    /\ IsLeader(n)
    /\ clock + LeaseDuration > lease.expiry
    /\ lease' = [lease EXCEPT !.expiry = clock + LeaseDuration]
    /\ leaseEnd' = [leaseEnd EXCEPT ![n] = clock + LeaseDuration]
    /\ UNCHANGED << clock, leaseEpoch, logVars, ckptVars, crashes >>

(* Log replication *)

AppendEntry(n) ==
    /\ IsLeader(n)
    /\ logEnd < MaxIndex
    /\ logEnd' = logEnd + 1
    /\ matchIdx' = [matchIdx EXCEPT ![n] = logEnd + 1]
    /\ UNCHANGED << clock, leaseVars, commitIndex, applied, ckptVars, crashes >>

\* Replica n durably stores the next log entry.
Replicate(n) ==
    /\ matchIdx[n] < logEnd
    /\ matchIdx' = [matchIdx EXCEPT ![n] = matchIdx[n] + 1]
    /\ UNCHANGED << clock, leaseVars, logEnd, commitIndex, applied,
                    ckptVars, crashes >>

\* The leader commits the next entry once a quorum stores it.
AdvanceCommit(n) ==
    /\ IsLeader(n)
    /\ commitIndex < logEnd
    /\ Quorum({m \in Nodes : matchIdx[m] > commitIndex})
    /\ commitIndex' = commitIndex + 1
    /\ UNCHANGED << clock, leaseVars, logEnd, matchIdx, applied,
                    ckptVars, crashes >>

\* Replica n applies the next committed entry it stores.
Apply(n) ==
    /\ applied[n] < Min(matchIdx[n], commitIndex)
    /\ applied' = [applied EXCEPT ![n] = applied[n] + 1]
    /\ UNCHANGED << clock, leaseVars, logEnd, matchIdx, commitIndex,
                    ckptVars, crashes >>

\* Crash and restart. Volatile state is lost. The replica restores its
\* durable snapshot and must replay log entries above it. Its lease belief
\* is also forgotten, which is conservative.
Crash(n) ==
    /\ crashes < MaxCrashes
    /\ crashes' = crashes + 1
    /\ applied' = [applied EXCEPT ![n] = snap[n]]
    /\ leaseEnd' = [leaseEnd EXCEPT ![n] = 0]
    /\ UNCHANGED << clock, lease, leaseEpoch, logEnd, matchIdx, commitIndex,
                    ckptVars >>

(* Checkpoint protocol *)

\* The leader proposes a checkpoint at a committed index above the current checkpoint.
ProposeCheckpoint(n, i) ==
    /\ IsLeader(n)
    /\ proposalIdx = 0
    /\ i > checkpointIdx
    /\ i <= commitIndex
    /\ proposalIdx' = i
    /\ proposalEpoch' = leaseEpoch[n]
    /\ acks' = {}
    /\ msgs' = msgs \cup {[idx |-> i, epoch |-> leaseEpoch[n], dst |-> d] : d \in Nodes}
    /\ UNCHANGED << clock, leaseVars, logVars, snap, checkpointIdx, truncIdx, crashes >>

\* The leader resends the proposal to a replica that has not acknowledged it yet.
Retransmit(n, d) ==
    /\ IsLeader(n)
    /\ proposalIdx > 0
    /\ proposalEpoch = leaseEpoch[n]
    /\ d \notin acks
    /\ LET m == [idx |-> proposalIdx, epoch |-> proposalEpoch, dst |-> d]
       IN /\ m \notin msgs
          /\ msgs' = msgs \cup {m}
    /\ UNCHANGED << clock, leaseVars, logVars, snap, proposalIdx, proposalEpoch,
                    acks, checkpointIdx, truncIdx, crashes >>

\* A replica receives a current proposal and has applied through its index.
\* The replica takes a durable snapshot at that index and acknowledges.
Deliver(m) ==
    /\ m \in msgs
    /\ m.idx = proposalIdx
    /\ m.epoch = proposalEpoch
    /\ applied[m.dst] >= m.idx
    /\ snap' = [snap EXCEPT ![m.dst] = Max(snap[m.dst], m.idx)]
    /\ acks' = acks \cup {m.dst}
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED << clock, leaseVars, logVars, proposalIdx, proposalEpoch,
                    checkpointIdx, truncIdx, crashes >>

\* The network loses a message. This also discards stale messages.
LoseMsg(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED << clock, leaseVars, logVars, snap, proposalIdx, proposalEpoch,
                    acks, checkpointIdx, truncIdx, crashes >>

\* Finalization requires an effective lease in the proposal's epoch.
\* It also requires acks from every member, active or potentially active.
FinalizeCheckpoint(n) ==
    /\ IsLeader(n)
    /\ proposalIdx > 0
    /\ proposalEpoch = leaseEpoch[n]
    /\ acks = Nodes
    /\ proposalIdx <= commitIndex
    /\ checkpointIdx' = Max(checkpointIdx, proposalIdx)
    /\ proposalIdx' = 0
    /\ acks' = {}
    /\ UNCHANGED << clock, leaseVars, logVars, snap, proposalEpoch, msgs,
                    truncIdx, crashes >>

\* The leader compacts the log up to the finalized checkpoint.
\* Every replica's durable snapshot must cover the truncated prefix.
Truncate(n) ==
    /\ IsLeader(n)
    /\ truncIdx < checkpointIdx
    /\ \A m \in Nodes : snap[m] >= checkpointIdx
    /\ truncIdx' = checkpointIdx
    /\ UNCHANGED << clock, leaseVars, logVars, snap, proposalIdx, proposalEpoch,
                    acks, msgs, checkpointIdx, crashes >>

---------------------------------------------------------------------------------------------
Next ==
    \/ Tick
    \/ \E n \in Nodes :
          \/ AcquireLease(n)
          \/ RenewLease(n)
          \/ AppendEntry(n)
          \/ Replicate(n)
          \/ AdvanceCommit(n)
          \/ Apply(n)
          \/ Crash(n)
          \/ FinalizeCheckpoint(n)
          \/ Truncate(n)
          \/ \E i \in 1..MaxIndex : ProposeCheckpoint(n, i)
          \/ \E d \in Nodes : Retransmit(n, d)
    \/ \E m \in msgs : Deliver(m) \/ LoseMsg(m)

\* "Sufficiently reliable communication" has three parts. First, replicas
\* eventually replicate and apply entries. Second, the leader keeps
\* retransmitting. Third, a message that is repeatedly deliverable is
\* eventually delivered (strong fairness despite losses).
Fairness ==
    /\ \A n \in Nodes :
          /\ WF_vars(Replicate(n))
          /\ WF_vars(Apply(n))
          /\ WF_vars(AdvanceCommit(n))
          /\ WF_vars(FinalizeCheckpoint(n))
          /\ WF_vars(Truncate(n))
          /\ \A d \in Nodes : WF_vars(Retransmit(n, d))
    /\ \A m \in MsgType : SF_vars(Deliver(m))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------------
(* Safety invariants *)

\* Exclusivity of effective lease ownership. Under zero-drift timing,
\* no overlap is permitted.
LeaseExclusivity ==
    \A m, n \in Nodes : (m /= n) => ~(LeaseEffective(m) /\ LeaseEffective(n))

\* No node's lease belief extends beyond the authoritative lease record.
\* Only the current holder may hold the current epoch.
LeaseBeliefBounded ==
    \A n \in Nodes :
        /\ leaseEnd[n] <= lease.expiry
        /\ (LeaseEffective(n) => (lease.holder = n /\ leaseEpoch[n] = lease.epoch))

\* Ordering of truncation point, checkpoint, commit and log.
CheckpointOrdering ==
    /\ truncIdx <= checkpointIdx
    /\ checkpointIdx <= commitIndex
    /\ commitIndex <= logEnd
    /\ (proposalIdx > 0) => (proposalIdx > checkpointIdx /\ proposalIdx <= commitIndex)

\* No entry still needed by any active or potentially active replica is discarded.
\* After a restart, a replica replays from snap[n]+1, so those entries must remain.
NoNeededEntryDiscarded ==
    \A n \in Nodes :
        /\ snap[n] >= truncIdx
        /\ snap[n] <= applied[n]
        /\ applied[n] <= matchIdx[n]
        /\ applied[n] <= commitIndex

\* Every committed entry is preserved. It remains in the log, or it is
\* covered by every replica's durable snapshot.
CommittedEntriesPreserved ==
    \A i \in 1..commitIndex :
        \/ (i > truncIdx /\ i <= logEnd)
        \/ (\A n \in Nodes : snap[n] >= i)

\* Committed entries stay durable on a quorum, so they survive leader changes.
CommittedOnQuorum ==
    \A i \in 1..commitIndex :
        \/ Quorum({n \in Nodes : matchIdx[n] >= i})
        \/ (\A n \in Nodes : snap[n] >= i)

\* Acks for the pending proposal are all backed by durable snapshots.
AcksBackedBySnapshots ==
    \A n \in acks : proposalIdx > 0 /\ snap[n] >= proposalIdx

Safety ==
    /\ TypeOK
    /\ LeaseExclusivity
    /\ LeaseBeliefBounded
    /\ CheckpointOrdering
    /\ NoNeededEntryDiscarded
    /\ CommittedEntriesPreserved
    /\ CommittedOnQuorum
    /\ AcksBackedBySnapshots

(* Action properties *)

\* Checkpoint, truncation, commit and snapshot indices are monotone.
\* Lease epochs never decrease.
Monotonicity ==
    [][ /\ checkpointIdx' >= checkpointIdx
        /\ truncIdx' >= truncIdx
        /\ commitIndex' >= commitIndex
        /\ lease'.epoch >= lease.epoch
        /\ \A n \in Nodes : snap'[n] >= snap[n] ]_vars

\* Checkpoint decisions respect lease ownership. Advancing the checkpoint or
\* the truncation point requires a node that holds a valid lease.
CheckpointRespectsLease ==
    [][ (checkpointIdx' /= checkpointIdx \/ truncIdx' /= truncIdx)
          => \E n \in Nodes : IsLeader(n) ]_vars

\* Only a lease holder that is still valid can extend the lease
\* within the same epoch.
LeaseRenewalRespectsOwnership ==
    [][ (lease'.epoch = lease.epoch /\ lease'.expiry /= lease.expiry)
          => IsLeader(lease.holder) ]_vars

---------------------------------------------------------------------------------------------
(* Liveness properties *)

LeaderStable == lease.holder \in Nodes /\ LeaseEffective(lease.holder)

\* With a stable leader holding a valid lease, every proposed checkpoint
\* index is eventually finalized.
CheckpointCompletes ==
    (<>[]LeaderStable) =>
        \A i \in 1..MaxIndex : (proposalIdx = i) ~> (checkpointIdx >= i)

\* With a stable leader, the safe truncation point eventually catches up
\* with every finalized checkpoint.
TruncationAdvances ==
    (<>[]LeaderStable) =>
        \A i \in 1..MaxIndex : (checkpointIdx >= i) ~> (truncIdx >= i)

Liveness == CheckpointCompletes /\ TruncationAdvances

THEOREM Spec => []Safety
THEOREM Spec => Monotonicity /\ CheckpointRespectsLease /\ LeaseRenewalRespectsOwnership
THEOREM Spec => Liveness
=============================================================================================