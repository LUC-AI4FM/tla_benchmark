---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    sched       \* sequence of clients whose requests may be served (schedule)

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Type definitions *)

TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Set of all currently available (unallocated) resources
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of clients with outstanding unsatisfied requests
requesting == {c \in Clients : unsat[c] /= {}}

\* A client is eligible to make a new request if it has no outstanding request and holds no resources
canRequest(c) == unsat[c] = {} /\ alloc[c] = {}

\* Convert sequence to set of elements
SeqToSet(s) == {s[i] : i \in 1..Len(s)}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

\* Client c requests a non-empty set S of resources
\* Only allowed when client has no outstanding request and holds no resources
Request(c, S) ==
    /\ canRequest(c)
    /\ S /= {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = sched

\* Schedule a requesting client that is not already scheduled
Schedule(c) ==
    /\ c \in requesting
    /\ c \notin SeqToSet(sched)
    /\ sched' = Append(sched, c)
    /\ unsat' = unsat
    /\ alloc' = alloc

\* Allocate a non-empty subset S of available resources to the first scheduled client
\* The allocated resources must be from what the client requested (intersection with unsat)
Allocate(c, S) ==
    /\ Len(sched) > 0
    /\ c = Head(sched)
    /\ S /= {}
    /\ S \subseteq available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    \* Remove client from schedule if fully satisfied
    /\ sched' = IF unsat'[c] = {} THEN Tail(sched) ELSE sched

\* Client c returns a non-empty subset S of its allocated resources
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : Schedule(c)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Fairness conditions *)

\* A client is fully satisfied when it has resources and no outstanding requests
fullySatisfied(c) == alloc[c] /= {} /\ unsat[c] = {}

\* Weak fairness for returning resources when fully satisfied
ReturnFairness == \A c \in Clients : WF_vars(\E S \in SUBSET alloc[c] : S /= {} /\ Return(c, S))

\* Weak fairness for allocation - allocations eventually happen when enabled
AllocateFairness == WF_vars(\E c \in Clients, S \in SUBSET Resources : Allocate(c, S))

\* Weak fairness for scheduling - scheduling eventually occurs when enabled
ScheduleFairness == WF_vars(\E c \in Clients : Schedule(c))

Fairness == ReturnFairness /\ AllocateFairness /\ ScheduleFairness

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Mutual exclusion: no resource is allocated to more than one client
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

\* Allocator invariant: all allocated and unsatisfied resources are valid
AllocatorInvariant ==
    /\ \A c \in Clients : alloc[c] \subseteq Resources
    /\ \A c \in Clients : unsat[c] \subseteq Resources
    \* Unsatisfied requests don't overlap with already allocated resources for that client
    /\ \A c \in Clients : alloc[c] \cap unsat[c] = {}

\* Combined safety invariant
Safety == TypeOK /\ MutualExclusion /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Eventual return: if a client holds resources with no outstanding request, it eventually returns them
EventualReturn ==
    \A c \in Clients : fullySatisfied(c) ~> alloc[c] = {}

\* Eventual obtainment: if a client requests resources, it eventually gets them all
EventualObtainment ==
    \A c \in Clients : unsat[c] /= {} ~> (unsat[c] = {} /\ alloc[c] /= {})

\* Infinitely often satisfied: clients are infinitely often in a state where they have no pending requests
InfinitelyOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {})

\* Combined liveness property
Liveness == EventualReturn /\ EventualObtainment /\ InfinitelyOftenSatisfied

=============================================================================