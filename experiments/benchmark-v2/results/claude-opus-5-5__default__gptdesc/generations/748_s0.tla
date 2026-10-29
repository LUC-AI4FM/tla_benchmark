------------------------- MODULE MCCheckpointCoordination -------------------------
EXTENDS Naturals, FiniteSets, TLC

----------------------------- MODULE CheckpointCoordination -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,           \* Set of nodes participating in checkpoint coordination
    NoNode,         \* Sentinel value meaning "no lease holder"
    NatRange,       \* Range of natural numbers used for time / lease expiry
    LogIndex,       \* Set of log indices
    LeaseDuration   \* Duration of a checkpoint lease

ASSUME NoNode \notin Node
ASSUME 0 \in NatRange
ASSUME LeaseDuration \in Nat

VARIABLES
    leader,         \* Current leader node
    log,            \* Log contents: each index is Open or Filled
    lease,          \* Checkpoint lease: [holder, expiry]
    clock,          \* Global logical clock
    checkpointing,  \* Set of nodes currently performing a checkpoint
    checkpointed    \* Highest log index covered by a completed checkpoint

vars == <<leader, log, lease, clock, checkpointing, checkpointed>>

Open   == "Open"
Filled == "Filled"

IsOpen(i) == log[i] = Open

FilledIndices == {i \in LogIndex : log[i] = Filled}

HighestFilled ==
    IF FilledIndices = {}
    THEN 0
    ELSE CHOOSE i \in FilledIndices : \A j \in FilledIndices : j <= i

LeaseValid(n) == lease.holder = n /\ clock <= lease.expiry

TypeOK ==
    /\ leader \in Node
    /\ log \in [LogIndex -> {Open, Filled}]
    /\ lease \in [holder : Node \cup {NoNode}, expiry : NatRange]
    /\ clock \in NatRange
    /\ checkpointing \subseteq Node
    /\ checkpointed \in {0} \cup LogIndex

Init ==
    /\ leader \in Node
    /\ log = [i \in LogIndex |-> Open]
    /\ lease = [holder |-> NoNode, expiry |-> 0]
    /\ clock = 0
    /\ checkpointing = {}
    /\ checkpointed = 0

\* The correct lease-replacement predicate: a lease may be replaced only if
\* nobody holds it, or it has expired and its holder is not mid-checkpoint.
CanReplaceLease(n) ==
    /\ lease.holder # n
    /\ \/ lease.holder = NoNode
       \/ /\ clock > lease.expiry
          /\ lease.holder \notin checkpointing

Tick ==
    /\ clock + 1 \in NatRange
    /\ clock' = clock + 1
    /\ UNCHANGED <<leader, log, lease, checkpointing, checkpointed>>

ElectLeader(n) ==
    /\ n # leader
    /\ leader' = n
    /\ UNCHANGED <<log, lease, clock, checkpointing, checkpointed>>

AppendEntry ==
    /\ \E i \in LogIndex :
          /\ IsOpen(i)
          /\ (\A j \in LogIndex : (j < i) => ~IsOpen(j))
          /\ log' = [log EXCEPT ![i] = Filled]
    /\ UNCHANGED <<leader, lease, clock, checkpointing, checkpointed>>

TakeLeaseWith(Pred(_), n) ==
    /\ Pred(n)
    /\ clock + LeaseDuration \in NatRange
    /\ lease' = [holder |-> n, expiry |-> clock + LeaseDuration]
    /\ UNCHANGED <<leader, log, clock, checkpointing, checkpointed>>

TakeLease(n) == TakeLeaseWith(CanReplaceLease, n)

ReleaseLease(n) ==
    /\ lease.holder = n
    /\ n \notin checkpointing
    /\ lease' = [holder |-> NoNode, expiry |-> 0]
    /\ UNCHANGED <<leader, log, clock, checkpointing, checkpointed>>

StartCheckpoint(n) ==
    /\ LeaseValid(n)
    /\ n \notin checkpointing
    /\ HighestFilled > checkpointed
    /\ checkpointing' = checkpointing \cup {n}
    /\ UNCHANGED <<leader, log, lease, clock, checkpointed>>

FinishCheckpoint(n) ==
    /\ n \in checkpointing
    /\ checkpointing' = checkpointing \ {n}
    /\ checkpointed' = HighestFilled
    /\ UNCHANGED <<leader, log, lease, clock>>

NextWith(Pred(_)) ==
    \/ Tick
    \/ AppendEntry
    \/ \E n \in Node :
          \/ ElectLeader(n)
          \/ TakeLeaseWith(Pred, n)
          \/ ReleaseLease(n)
          \/ StartCheckpoint(n)
          \/ FinishCheckpoint(n)

Next == NextWith(CanReplaceLease)

Spec == Init /\ [][Next]_vars

\* Safety invariants
AtMostOneCheckpointer == Cardinality(checkpointing) <= 1

CheckpointerHoldsLease == \A n \in checkpointing : lease.holder = n

CheckpointBounded == checkpointed <= HighestFilled

Safety == AtMostOneCheckpointer /\ CheckpointerHoldsLease /\ CheckpointBounded
=========================================================================================