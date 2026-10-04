---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    sched       \* sequence of clients whose requests may be served, in priority order

vars == <<unsat, alloc, sched>>

----------------------------------------------------------------------------
\* Type definitions

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

\* Set of all resources currently allocated
AllocatedResources == UNION {alloc[c] : c \in Clients}

\* Set of resources that are available (not allocated to anyone)
Available == Resources \ AllocatedResources

\* Set of clients with outstanding unsatisfied requests
RequestingClients == {c \in Clients : unsat[c] /= {}}

\* Set of clients in the schedule
ScheduledClients == {sched[i] : i \in 1..Len(sched)}

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

----------------------------------------------------------------------------
\* Actions

\* Client c requests a non-empty set S of resources
\* Precondition: c has no outstanding request and holds no resources
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S /= {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = sched

\* Allocate a non-empty subset S of requested resources to client c
\* c must be first in schedule with unsat requests, S must be available
Allocate(c, S) ==
    /\ sched /= <<>>
    /\ c = Head(sched)
    /\ S /= {}
    /\ S \subseteq unsat[c]
    /\ S \subseteq Available
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ sched' = sched

\* Client c returns a non-empty subset S of its allocated resources
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

\* Schedule a requesting client c that is not already scheduled
Schedule(c) ==
    /\ unsat[c] /= {}
    /\ c \notin ScheduledClients
    /\ sched' = Append(sched, c)
    /\ unsat' = unsat
    /\ alloc' = alloc

\* Remove a client from the front of the schedule when fully satisfied
Unschedule ==
    /\ sched /= <<>>
    /\ unsat[Head(sched)] = {}
    /\ sched' = Tail(sched)
    /\ unsat' = unsat
    /\ alloc' = alloc

----------------------------------------------------------------------------
\* Next state relation

Next ==
    \/ \E c \in Clients : \E S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Return(c, S)
    \/ \E c \in Clients : Schedule(c)
    \/ Unschedule

----------------------------------------------------------------------------
\* Fairness conditions

\* Client returns resources once fully satisfied (unsat = {} and alloc /= {})
ClientReturnsFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET alloc[c] : S /= {} /\ Return(c, S))

\* Allocations eventually happen when enabled
AllocationFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

\* Scheduling eventually occurs
SchedulingFairness ==
    \A c \in Clients : WF_vars(Schedule(c))

\* Unscheduling fairness
UnschedulingFairness == WF_vars(Unschedule)

Fairness ==
    /\ ClientReturnsFairness
    /\ AllocationFairness
    /\ SchedulingFairness
    /\ UnschedulingFairness

----------------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Safety Invariants

\* Mutual exclusion: no resource is allocated to more than one client
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

\* Allocator invariant: scheduled clients have unsatisfied requests, and
\* the schedule contains no duplicates
AllocatorInvariant ==
    /\ \A i \in 1..Len(sched) : unsat[sched[i]] /= {}
    /\ \A i, j \in 1..Len(sched) : i /= j => sched[i] /= sched[j]

\* Resources are only allocated from what was requested or still unsatisfied
\* (allocated resources were originally requested)
AllocationConsistency ==
    \A c \in Clients : alloc[c] \cap unsat[c] = {}

\* Safety invariant combining all safety properties
Safety ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ AllocatorInvariant
    /\ AllocationConsistency

----------------------------------------------------------------------------
\* Liveness Properties

\* Eventually, if a client holds resources and is satisfied, it returns them
EventualReturn ==
    \A c \in Clients : (alloc[c] /= {} /\ unsat[c] = {}) ~> (alloc[c] = {})

\* Eventually, every requested resource is obtained (request is satisfied)
EventualObtainment ==
    \A c \in Clients : unsat[c] /= {} ~> unsat[c] = {}

\* Infinitely often, some client's request is satisfied
InfinitelyOftenSatisfied ==
    []<>(\E c \in Clients : unsat[c] = {} /\ alloc[c] /= {})

\* Combined liveness (for checking)
Liveness ==
    /\ EventualReturn
    /\ EventualObtainment

=============================================================================