---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Clients, Resources

VARIABLES
    requests,      \* requests[c] = set of resources client c is currently requesting
    allocations,   \* allocations[c] = set of resources currently held by client c
    schedule       \* sequence of clients with outstanding requests, in scheduling order

vars == <<requests, allocations, schedule>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ allocations \in [Clients -> SUBSET Resources]
    /\ schedule \in Seq(Clients)

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Set of all resources currently held by any client
HeldResources == UNION {allocations[c] : c \in Clients}

\* Set of resources that are available (not held by anyone)
AvailableResources == Resources \ HeldResources

\* Set of clients that appear in the schedule
ScheduledClients == {schedule[i] : i \in 1..Len(schedule)}

\* Clients with outstanding requests (requesting something they don't have yet)
RequestingClients == {c \in Clients : requests[c] \ allocations[c] # {}}

\* Position of client c in schedule (0 if not scheduled)
Position(c) == 
    IF c \in ScheduledClients 
    THEN CHOOSE i \in 1..Len(schedule) : schedule[i] = c
    ELSE 0

\* Clients earlier than c in the schedule
EarlierClients(c) ==
    IF Position(c) = 0 THEN {}
    ELSE {schedule[i] : i \in 1..(Position(c)-1)}

\* Resources requested by clients earlier than c in schedule
EarlierRequests(c) ==
    UNION {requests[e] \ allocations[e] : e \in EarlierClients(c)}

\* Resources that can be allocated to client c (available and not requested by earlier clients)
AllocatableFor(c) ==
    (requests[c] \ allocations[c]) \cap AvailableResources \ EarlierRequests(c)

\* Check if allocation is possible for some client
AllocationPossible ==
    \E c \in ScheduledClients : AllocatableFor(c) # {}

\* A client can make a new request only if previous request fully satisfied and no held resources
CanRequest(c) ==
    /\ requests[c] = {}
    /\ allocations[c] = {}

\* A client's request is fully satisfied
RequestSatisfied(c) ==
    requests[c] # {} /\ requests[c] = allocations[c]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ allocations = [c \in Clients |-> {}]
    /\ schedule = <<>>

-----------------------------------------------------------------------------
(* Actions *)

\* Client c issues a new request for a non-empty subset S of resources
Request(c, S) ==
    /\ CanRequest(c)
    /\ S # {}
    /\ S \subseteq Resources
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<allocations, schedule>>

\* Allocator extends schedule by inserting requesting but unscheduled clients
\* newOrder is an arbitrary sequence of currently unscheduled requesting clients
ExtendSchedule(newOrder) ==
    /\ LET unscheduled == RequestingClients \ ScheduledClients
       IN /\ unscheduled # {}
          /\ {newOrder[i] : i \in 1..Len(newOrder)} = unscheduled
          /\ \A i, j \in 1..Len(newOrder) : i # j => newOrder[i] # newOrder[j]
    /\ schedule' = schedule \o newOrder
    /\ UNCHANGED <<requests, allocations>>

\* Allocator grants a non-empty subset S of allocatable resources to scheduled client c
Allocate(c, S) ==
    /\ c \in ScheduledClients
    /\ S # {}
    /\ S \subseteq AllocatableFor(c)
    /\ allocations' = [allocations EXCEPT ![c] = @ \cup S]
    /\ UNCHANGED <<requests, schedule>>

\* Client c returns all held resources after request is satisfied
Return(c) ==
    /\ RequestSatisfied(c)
    /\ requests' = [requests EXCEPT ![c] = {}]
    /\ allocations' = [allocations EXCEPT ![c] = {}]
    \* Remove c from schedule
    /\ schedule' = SelectSeq(schedule, LAMBDA x : x # c)

\* Remove clients from schedule that no longer have outstanding requests
CleanSchedule ==
    /\ \E c \in ScheduledClients : requests[c] \ allocations[c] = {}
    /\ schedule' = SelectSeq(schedule, LAMBDA c : requests[c] \ allocations[c] # {})
    /\ UNCHANGED <<requests, allocations>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E newOrder \in Seq(Clients) : 
          /\ Len(newOrder) <= Cardinality(Clients)
          /\ ExtendSchedule(newOrder)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients : Return(c)
    \/ CleanSchedule

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Mutual exclusion: resources are never held concurrently by more than one client
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => allocations[c1] \cap allocations[c2] = {}

\* A client never holds a resource requested by an earlier client in schedule
NoEarlierConflict ==
    \A c \in Clients : allocations[c] \cap EarlierRequests(c) = {}

\* Scheduled clients always correspond to clients with outstanding requests
ScheduleValidity ==
    /\ \A i \in 1..Len(schedule) : schedule[i] \in RequestingClients
    /\ \A i, j \in 1..Len(schedule) : i # j => schedule[i] # schedule[j]

\* Combined safety invariant
Safety == MutualExclusion /\ NoEarlierConflict /\ ScheduleValidity

\* Allocation feasibility: for every scheduled client, every remaining requested 
\* resource must be reachable assuming earlier scheduled clients eventually release
AllocationFeasibility ==
    \A c \in ScheduledClients :
        \A r \in (requests[c] \ allocations[c]) :
            r \in Resources

Invariant == TypeOK /\ Safety /\ AllocationFeasibility

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Fairness assumptions
\* Clients eventually return after satisfaction
ClientFairness ==
    \A c \in Clients : WF_vars(Return(c))

\* Allocator eventually makes progress when possible
AllocatorFairness ==
    \A c \in Clients : 
        WF_vars(\E S \in SUBSET Resources : S # {} /\ Allocate(c, S))

\* Allocator eventually schedules requesting clients
SchedulingFairness ==
    WF_vars(\E newOrder \in Seq(Clients) : 
                /\ Len(newOrder) <= Cardinality(Clients)
                /\ ExtendSchedule(newOrder))

\* Combined fairness
Fairness == ClientFairness /\ AllocatorFairness /\ SchedulingFairness

\* Full specification with liveness
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Liveness Guarantees *)

\* Every requested resource is eventually allocated
EventualAllocation ==
    \A c \in Clients : \A r \in Resources :
        (r \in requests[c]) ~> (r \in allocations[c])

\* Each client's requests are satisfied infinitely often
\* (whenever a client makes a request, it eventually gets satisfied)
InfinitelySatisfied ==
    \A c \in Clients :
        [](requests[c] # {} => <>(RequestSatisfied(c)))

\* Any requesting client eventually gets scheduled
EventualScheduling ==
    \A c \in Clients :
        (c \in RequestingClients) ~> (c \in ScheduledClients)

\* Combined liveness property
Liveness == EventualAllocation /\ EventualScheduling

=============================================================================