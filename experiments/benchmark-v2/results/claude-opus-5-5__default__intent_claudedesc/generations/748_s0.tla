------------------------- MODULE CheckpointLeaseCoordination -------------------------
(***************************************************************************)
(* Checkpoint coordination over a replicated log.                          *)
(*                                                                         *)
(* A lease grants its holder the right to checkpoint ("close") log         *)
(* indices. Once an index is closed, it is checkpointed and must never be  *)
(* covered by a later lease. A node acquires a lease by proposing a lease  *)
(* request. The request records the lease it observed ("prev") and asks    *)
(* for a start index just above the indices closed under that lease.       *)
(*                                                                         *)
(* All proposals go through the designated Leader, which appends them to   *)
(* the replicated log. Entries are applied in log order. Between proposal  *)
(* and application, the current lease holder may close more indices.       *)
(*                                                                         *)
(* ShouldReplaceLease decides whether an applied lease request takes       *)
(* effect. The correct rule replaces the lease only if the request was     *)
(* evaluated against exactly the current lease. The proposed optimization  *)
(* also replaces the lease whenever the current holder is the leader.      *)
(* Set UseLeaderOptimization = TRUE and TLC finds a violation of           *)
(* LeaseSafety, which shows the optimization is incorrect.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,                  \* set of node identifiers
    Leader,                 \* the designated leader node
    MaxIndex,               \* log indices / checkpoint positions are 1..MaxIndex
    MaxLogLen,              \* bound on replicated log length (model checking)
    UseLeaderOptimization   \* TRUE => use the (unsafe) leader shortcut

ASSUME /\ Leader \in Nodes
       /\ MaxIndex \in Nat /\ MaxIndex >= 2
       /\ MaxLogLen \in Nat /\ MaxLogLen >= 1
       /\ UseLeaderOptimization \in BOOLEAN

VARIABLES
    log,          \* replicated log: sequence of entries
    applied,      \* index of the last applied log entry
    lease,        \* currently applied lease record
    maxClosed,    \* highest index ever closed (checkpointed) under any lease
    priorClosed,  \* value of maxClosed when the current lease was installed
    proposals     \* proposals sent to the leader but not yet appended

vars == <<log, applied, lease, maxClosed, priorClosed, proposals>>

-----------------------------------------------------------------------------
(* Bounded sets for model checking *)
Indices  == 1..MaxIndex
NatModel == 0..MaxLogLen

Max(a, b) == IF a >= b THEN a ELSE b

LeaseRec == [holder : Nodes, seq : NatModel, start : Indices, closed : 0..MaxIndex]

Entry == [type : {"lease", "close"}, holder : Nodes, prev : LeaseRec,
          start : 0..MaxIndex, ts : 0..MaxIndex]

(* Indices that are still open, i.e. not yet closed or checkpointed *)
OpenIndices == {i \in Indices : i > maxClosed /\ i > lease.closed}

-----------------------------------------------------------------------------
(* Lease replacement logic *)

\* Correct rule: the request was evaluated against the current lease state.
ShouldReplaceLeaseCorrect(e) == e.prev = lease

\* Proposed optimization: also replace whenever the current holder is the
\* leader. This is incorrect.
ShouldReplaceLeaseOptimized(e) ==
    \/ e.prev = lease
    \/ lease.holder = Leader

ShouldReplaceLease(e) ==
    IF UseLeaderOptimization
        THEN ShouldReplaceLeaseOptimized(e)
        ELSE ShouldReplaceLeaseCorrect(e)

-----------------------------------------------------------------------------
Init ==
    /\ log = <<>>
    /\ applied = 0
    /\ lease = [holder |-> Leader, seq |-> 0, start |-> 1, closed |-> 0]
    /\ maxClosed = 0
    /\ priorClosed = 0
    /\ proposals = {}

(* Node n (not the current holder) requests the lease, based on its view. *)
ProposeLease(n) ==
    /\ n # lease.holder
    /\ lease.closed + 1 <= MaxIndex
    /\ proposals' = proposals \cup
         {[type |-> "lease", holder |-> n, prev |-> lease,
           start |-> lease.closed + 1, ts |-> 0]}
    /\ UNCHANGED <<log, applied, lease, maxClosed, priorClosed>>

(* The lease holder proposes to close (checkpoint) an open index. The last *)
(* index is never closed, so some index always stays open.                 *)
ProposeClose(n, ts) ==
    /\ n = lease.holder
    /\ ts \in OpenIndices
    /\ ts < MaxIndex
    /\ proposals' = proposals \cup
         {[type |-> "close", holder |-> n, prev |-> lease,
           start |-> 0, ts |-> ts]}
    /\ UNCHANGED <<log, applied, lease, maxClosed, priorClosed>>

(* The leader appends a pending proposal to the replicated log. *)
LeaderAppend(p) ==
    /\ p \in proposals
    /\ Len(log) < MaxLogLen
    /\ log' = Append(log, p)
    /\ proposals' = proposals \ {p}
    /\ UNCHANGED <<applied, lease, maxClosed, priorClosed>>

(* A proposal is lost before it is appended. *)
DropProposal(p) ==
    /\ p \in proposals
    /\ proposals' = proposals \ {p}
    /\ UNCHANGED <<log, applied, lease, maxClosed, priorClosed>>

(* Apply the next log entry deterministically on all replicas. *)
ApplyEntry ==
    /\ applied < Len(log)
    /\ LET e == log[applied + 1] IN
         IF e.type = "lease"
         THEN IF ShouldReplaceLease(e)
              THEN /\ lease' = [holder |-> e.holder,
                                seq    |-> lease.seq + 1,
                                start  |-> e.start,
                                closed |-> e.start - 1]
                   /\ priorClosed' = maxClosed
                   /\ UNCHANGED maxClosed
              ELSE UNCHANGED <<lease, maxClosed, priorClosed>>
         ELSE \* close entry: valid only under the lease it was proposed with
              IF e.prev.seq = lease.seq /\ e.ts > lease.closed
              THEN /\ lease' = [lease EXCEPT !.closed = e.ts]
                   /\ maxClosed' = Max(maxClosed, e.ts)
                   /\ UNCHANGED priorClosed
              ELSE UNCHANGED <<lease, maxClosed, priorClosed>>
    /\ applied' = applied + 1
    /\ UNCHANGED <<log, proposals>>

Next ==
    \/ \E n \in Nodes : ProposeLease(n)
    \/ \E n \in Nodes, ts \in Indices : ProposeClose(n, ts)
    \/ \E p \in proposals : LeaderAppend(p)
    \/ \E p \in proposals : DropProposal(p)
    \/ ApplyEntry

Spec == Init /\ [][Next]_vars /\ WF_vars(ApplyEntry)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ log \in Seq(Entry)
    /\ Len(log) <= MaxLogLen
    /\ applied \in 0..Len(log)
    /\ lease \in LeaseRec
    /\ maxClosed \in 0..MaxIndex
    /\ priorClosed \in 0..MaxIndex
    /\ proposals \subseteq Entry

\* Progress: some open indices always remain.
Progress == OpenIndices # {}

\* Safe lease replacement: a new lease never covers an index that was
\* already closed (checkpointed) under an earlier lease.
LeaseSafety == lease.start > priorClosed

\* Under the correct rule, the current lease reflects every closed index.
ClosedConsistent == maxClosed = lease.closed

Safety == TypeOK /\ Progress /\ LeaseSafety

(* Action properties *)
ClosedMonotonic == [][maxClosed' >= maxClosed]_vars
LeaseSeqMonotonic == [][lease'.seq >= lease.seq]_vars

(* Liveness: every appended entry is eventually applied. *)
EventuallyApplied ==
    \A k \in 1..MaxLogLen : (Len(log) >= k) ~> (applied >= k)

-----------------------------------------------------------------------------
(* Model checking support *)

\* Symmetry over non-leader nodes. The leader has a distinguished role.
Symmetry == Permutations(Nodes \ {Leader})

\* State constraint that keeps the explored state space bounded.
StateConstraint ==
    /\ Len(log) <= MaxLogLen
    /\ Cardinality(proposals) <= 2
    /\ lease.seq <= MaxLogLen

==============================================================================