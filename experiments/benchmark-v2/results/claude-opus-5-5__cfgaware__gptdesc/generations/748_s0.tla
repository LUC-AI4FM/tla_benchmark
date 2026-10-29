---------------------------- MODULE MCCheckpointCoordination ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,
    Majority,
    MaxLog,
    MaxNat,
    NoNode,
    NoCheckpointLease

ASSUME Majority \subseteq SUBSET Node
ASSUME MaxLog \in Nat /\ MaxNat \in Nat

VARIABLES
    log,
    clock,
    leader,
    checkpointing

vars == <<log, clock, leader, checkpointing>>

-----------------------------------------------------------------------------
\* Index ranges

LogIndex == Nat

\* Bounded ranges used for model checking
MCNat == 0 .. MaxNat

MCLogIndex == 0 .. MaxLog

-----------------------------------------------------------------------------
\* Log entries

OpenEntry == [type |-> "open"]

NoOpEntry == [type |-> "noop"]

CheckpointLease == [type : {"lease"}, node : Node, expiry : Nat]

LogEntry == {OpenEntry, NoOpEntry} \cup CheckpointLease

IsOpen(i) == log[i].type = "open"

IsFirstOpen(i) ==
    /\ IsOpen(i)
    /\ \A j \in LogIndex : j < i => ~IsOpen(j)

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

LeaseIndices == {i \in LogIndex : log[i].type = "lease"}

CurrentLease ==
    IF LeaseIndices = {}
    THEN NoCheckpointLease
    ELSE log[MaxOf(LeaseIndices)]

LeaseValid(l, n, t) ==
    /\ l # NoCheckpointLease
    /\ l.node = n
    /\ t <= l.expiry

IsLeaseExpired(l) ==
    \/ l = NoCheckpointLease
    \/ l.expiry < clock

-----------------------------------------------------------------------------
\* Lease replacement predicates

\* The correct predicate of the checkpoint coordination protocol
CC_CanReplaceLease(l) == IsLeaseExpired(l)

\* Bad optimization: also allow replacement whenever the lease is held
\* by the current leader. This is intentionally incorrect.
BadCanReplaceLease(l) ==
    \/ CC_CanReplaceLease(l)
    \/ (l # NoCheckpointLease /\ l.node = leader)

CanReplaceLease(l) == CC_CanReplaceLease(l)

-----------------------------------------------------------------------------
\* Actions

Init ==
    /\ log = [i \in LogIndex |-> OpenEntry]
    /\ clock = 0
    /\ leader = NoNode
    /\ checkpointing = {}

ElectLeader(n) ==
    /\ \E q \in Majority : n \in q
    /\ leader' = n
    /\ UNCHANGED <<log, clock, checkpointing>>

AppendNoOp ==
    /\ leader # NoNode
    /\ \E i \in LogIndex :
        /\ IsFirstOpen(i)
        /\ log' = [log EXCEPT ![i] = NoOpEntry]
    /\ UNCHANGED <<clock, leader, checkpointing>>

AppendLease(m) ==
    /\ leader # NoNode
    /\ CanReplaceLease(CurrentLease)
    /\ clock + 1 \in Nat
    /\ \E i \in LogIndex :
        /\ IsFirstOpen(i)
        /\ log' = [log EXCEPT ![i] =
                    [type |-> "lease", node |-> m, expiry |-> clock + 1]]
    /\ UNCHANGED <<clock, leader, checkpointing>>

StartCheckpoint(n) ==
    /\ n \notin checkpointing
    /\ LeaseValid(CurrentLease, n, clock)
    /\ checkpointing' = checkpointing \cup {n}
    /\ UNCHANGED <<log, clock, leader>>

FinishCheckpoint(n) ==
    /\ n \in checkpointing
    /\ checkpointing' = checkpointing \ {n}
    /\ UNCHANGED <<log, clock, leader>>

Tick ==
    /\ clock + 1 \in Nat
    /\ clock' = clock + 1
    /\ checkpointing' = {n \in checkpointing : LeaseValid(CurrentLease, n, clock + 1)}
    /\ UNCHANGED <<log, leader>>

Next ==
    \/ \E n \in Node : ElectLeader(n)
    \/ AppendNoOp
    \/ \E m \in Node : AppendLease(m)
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : FinishCheckpoint(n)
    \/ Tick

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
    /\ log \in [LogIndex -> LogEntry]
    /\ clock \in Nat
    /\ leader \in Node \cup {NoNode}
    /\ checkpointing \subseteq Node

SafetyInvariant ==
    \A n, m \in checkpointing : n = m

-----------------------------------------------------------------------------
\* Model checking helpers

StateConstraint == \E i \in LogIndex : IsOpen(i)

NodeSymmetry == Permutations(Node)

=============================================================================