------------------------------ MODULE TimestampAllocator ------------------------------
(***************************************************************************)
(* A logical timestamp allocator.  Requesters, identified by two distinct  *)
(* constant labels, nondeterministically submit timestamp requests.  The  *)
(* allocator serves pending requests in any interleaving.  Each issued     *)
(* timestamp must be strictly greater than the previously issued one, and  *)
(* strictly below the fixed numeric bound Limit.  When the bound is        *)
(* exhausted, pending requests are rejected rather than served, so the     *)
(* system never deadlocks.                                                 *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    L1, L2,     \* two distinct label values (timestamp requester identifiers)
    Limit       \* exclusive upper bound on issuable timestamps

ASSUME LabelsDistinct == L1 # L2
ASSUME LimitIsNat     == Limit \in Nat /\ Limit >= 1

Labels == {L1, L2}

\* Timestamp 0 is the "nothing issued yet" sentinel; real timestamps are
\* drawn from 1..(Limit - 1).
TimestampDomain == 1..(Limit - 1)

VARIABLES
    highest,    \* current highest issued timestamp (0 = none issued yet)
    available,  \* labels with no outstanding request (free to request)
    pending,    \* labels with an outstanding, unserved request
    issued      \* history: sequence of [label |-> l, ts |-> t] assignments

vars == << highest, available, pending, issued >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ highest \in 0..(Limit - 1)
    /\ available \subseteq Labels
    /\ pending \subseteq Labels
    /\ available \cap pending = {}
    /\ available \cup pending = Labels
    /\ issued \in Seq([label : Labels, ts : TimestampDomain])

\* Issuance is possible while some timestamp above `highest` remains
\* below the bound.
CanIssue == highest + 1 < Limit

-----------------------------------------------------------------------------
Init ==
    /\ highest = 0
    /\ available = Labels
    /\ pending = {}
    /\ issued = << >>

\* A requester with label l submits a request for a timestamp.
Request(l) ==
    /\ l \in available
    /\ available' = available \ {l}
    /\ pending' = pending \cup {l}
    /\ UNCHANGED << highest, issued >>

\* The allocator assigns to pending request l some timestamp strictly
\* greater than the current highest and strictly below the bound.
\* The exact choice is left nondeterministic (no implementation strategy
\* is prescribed).
Assign(l) ==
    /\ l \in pending
    /\ CanIssue
    /\ \E t \in (highest + 1)..(Limit - 1) :
          /\ highest' = t
          /\ issued' = Append(issued, [label |-> l, ts |-> t])
    /\ pending' = pending \ {l}
    /\ available' = available \cup {l}

\* When the bound has been reached, a pending request cannot be satisfied
\* and is rejected (no timestamp issued).
Reject(l) ==
    /\ l \in pending
    /\ ~CanIssue
    /\ pending' = pending \ {l}
    /\ available' = available \cup {l}
    /\ UNCHANGED << highest, issued >>

\* Serving a request means either assigning or (if exhausted) rejecting.
Serve(l) == Assign(l) \/ Reject(l)

Next ==
    \E l \in Labels : Request(l) \/ Serve(l)

\* Fair scheduling: each label's pending request is eventually served.
Fairness == \A l \in Labels : WF_vars(Serve(l))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Every issued timestamp is unique over the run.
UniqueTimestamps ==
    \A i, j \in 1..Len(issued) :
        i # j => issued[i].ts # issued[j].ts

\* The sequence of issued timestamps is strictly increasing.
StrictlyIncreasing ==
    \A i \in 1..(Len(issued) - 1) : issued[i].ts < issued[i + 1].ts

\* No issued timestamp reaches or exceeds the bound.
BoundRespected ==
    /\ highest < Limit
    /\ \A i \in 1..Len(issued) : issued[i].ts < Limit

\* `highest` faithfully records the most recently issued timestamp.
HighestConsistent ==
    IF Len(issued) = 0 THEN highest = 0
                       ELSE highest = issued[Len(issued)].ts

\* At most Limit - 1 timestamps can ever be issued.
IssueCountBounded == Len(issued) <= Limit - 1

SafetyInvariant ==
    /\ TypeOK
    /\ UniqueTimestamps
    /\ StrictlyIncreasing
    /\ BoundRespected
    /\ HighestConsistent
    /\ IssueCountBounded

\* Action-level safety: every step that issues a timestamp issues one
\* strictly greater than the previous highest and below the bound;
\* `highest` never decreases; history is only ever extended.
MonotonicIssuance ==
    [][ /\ highest' >= highest
        /\ Len(issued') >= Len(issued)
        /\ SubSeq(issued', 1, Len(issued)) = issued
        /\ (Len(issued') > Len(issued)) =>
              /\ Len(issued') = Len(issued) + 1
              /\ issued'[Len(issued')].ts > highest
              /\ issued'[Len(issued')].ts < Limit
              /\ highest' = issued'[Len(issued')].ts
      ]_vars

\* No deadlock: some action is always enabled.
NoDeadlock == ENABLED Next

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Weak liveness: if a request is outstanding and the bound still permits
\* issuance, a further timestamp is eventually issued.
ProgressWhileIssuable ==
    \A n \in 0..Limit :
        (pending # {} /\ CanIssue /\ Len(issued) = n) ~> (Len(issued) > n)

\* Every request is eventually served (assigned or, if exhausted, rejected).
EveryRequestServed ==
    \A l \in Labels : (l \in pending) ~> (l \notin pending)

\* A request made while issuance is possible is eventually answered, and
\* if it is answered while issuance is still possible, it receives a
\* timestamp.
RequestGetsTimestampWhenPossible ==
    \A l \in Labels :
        (l \in pending /\ CanIssue) ~>
            (l \notin pending \/ ~CanIssue)

LivenessProperties ==
    /\ ProgressWhileIssuable
    /\ EveryRequestServed
    /\ RequestGetsTimestampWhenPossible

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => MonotonicIssuance
THEOREM Spec => []NoDeadlock
THEOREM Spec => LivenessProperties
=============================================================================