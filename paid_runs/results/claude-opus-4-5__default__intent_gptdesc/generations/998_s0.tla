------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Resources,      \* The fixed finite set of reusable resources
    Clients         \* The set of clients

VARIABLES
    requests,       \* requests[c] = set of resources client c is currently requesting
    holding,        \* holding[c] = set of resources client c currently holds
    allocated,      \* allocated[c] = set of resources allocated to c (subset of requests[c])
    schedule        \* A sequence of clients with outstanding requests (scheduling order)

vars == <<requests, holding, allocated, schedule>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ holding \in [Clients -> SUBSET Resources]
    /\ allocated \in [Clients -> SUBSET Resources]
    /\ schedule \in Seq(Clients)

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Set of all resources currently held by any client
HeldResources == UNION {holding[c] : c \in Clients}

\* Set of all resources currently allocated (committed but maybe not yet held)
AllocatedResources == UNION {allocated[c] : c \in Clients}

\* All unavailable resources (held or allocated)
UnavailableResources == HeldResources \cup AllocatedResources

\* Available resources
AvailableResources == Resources \ UnavailableResources

\* Set of clients in the schedule
ScheduledClients == {schedule[i] : i \in 1..Len(schedule)}

\* Clients with outstanding requests
RequestingClients == {c \in Clients : requests[c] /= {}}

\* Position of client c in schedule (0 if not scheduled)
Position(c) ==
    IF c \in ScheduledClients
    THEN CHOOSE i \in 1..Len(schedule) : schedule[i] = c
    ELSE 0

\* Clients earlier than c in schedule
EarlierClients(c) ==
    IF Position(c) > 0
    THEN {schedule[i] : i \in 1..(Position(c)-1)}
    ELSE {}

\* Resources requested by clients earlier than c in schedule
EarlierRequestedResources(c) ==
    UNION {requests[c2] : c2 \in EarlierClients(c)}

\* Resources that can be allocated to client c without violating schedule order
\* (resources that c requests, are available, and not requested by earlier clients)
AllocatableToClient(c) ==
    (requests[c] \ allocated[c]) \cap AvailableResources \ EarlierRequestedResources(c)

\* Check if allocation is possible for client c
CanAllocate(c) == AllocatableToClient(c) /= {}

\* Check if any allocation is possible
SomeAllocationPossible == \E c \in ScheduledClients : CanAllocate(c)

\* Remaining requested resources for client c (not yet allocated)
RemainingRequests(c) == requests[c] \ allocated[c]

\* Resources held by clients earlier than c
EarlierHeldResources(c) ==
    UNION {holding[c2] : c2 \in EarlierClients(c)}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ holding = [c \in Clients |-> {}]
    /\ allocated = [c \in Clients |-> {}]
    /\ schedule = <<>>

-----------------------------------------------------------------------------
(* Actions *)

\* Client c issues a new request for a non-empty subset of resources
\* Precondition: c has no current request and holds no resources
Request(c, S) ==
    /\ S /= {}
    /\ S \subseteq Resources
    /\ requests[c] = {}
    /\ holding[c] = {}
    /\ allocated[c] = {}
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<holding, allocated, schedule>>

\* Allocator allocates a non-empty subset of allocatable resources to scheduled client c
Allocate(c, S) ==
    /\ c \in ScheduledClients
    /\ S /= {}
    /\ S \subseteq AllocatableToClient(c)
    /\ allocated' = [allocated EXCEPT ![c] = @ \cup S]
    /\ UNCHANGED <<requests, holding, schedule>>

\* Client c receives allocated resources (moves from allocated to holding)
ReceiveAllocation(c) ==
    /\ allocated[c] /= {}
    /\ holding' = [holding EXCEPT ![c] = @ \cup allocated[c]]
    /\ allocated' = [allocated EXCEPT ![c] = {}]
    /\ UNCHANGED <<requests, schedule>>

\* Client c returns all held resources after request is fully satisfied
\* Precondition: request is fully satisfied (all requested resources are held)
Return(c) ==
    /\ holding[c] /= {}
    /\ requests[c] \subseteq holding[c]  \* Request fully satisfied
    /\ allocated[c] = {}                  \* No pending allocations
    /\ holding' = [holding EXCEPT ![c] = {}]
    /\ requests' = [requests EXCEPT ![c] = {}]
    /\ schedule' = SelectSeq(schedule, LAMBDA x : x /= c)
    /\ UNCHANGED <<allocated>>

\* Allocator extends schedule by inserting currently requesting but unscheduled clients
\* in an arbitrary order
Schedule ==
    /\ \E unscheduled \in SUBSET (RequestingClients \ ScheduledClients) :
        /\ unscheduled /= {}
        /\ \E perm \in [1..Cardinality(unscheduled) -> unscheduled] :
            /\ \A i, j \in 1..Cardinality(unscheduled) : i /= j => perm[i] /= perm[j]
            /\ schedule' = schedule \o [i \in 1..Cardinality(unscheduled) |-> perm[i]]
    /\ UNCHANGED <<requests, holding, allocated>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients : ReceiveAllocation(c)
    \/ \E c \in Clients : Return(c)
    \/ Schedule

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Mutual exclusion: resources are never held concurrently by more than one client
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => holding[c1] \cap holding[c2] = {}

\* A client never holds a resource currently requested by any earlier client in schedule
NoHoldingEarlierRequested ==
    \A c \in Clients :
        holding[c] \cap EarlierRequestedResources(c) = {}

\* Scheduled clients always correspond to clients with outstanding requests
ScheduleConsistency ==
    /\ \A i \in 1..Len(schedule) : requests[schedule[i]] /= {}
    /\ \A i, j \in 1..Len(schedule) : i /= j => schedule[i] /= schedule[j]

\* Allocated resources are always a subset of requested resources
AllocationConsistency ==
    \A c \in Clients : allocated[c] \subseteq requests[c]

\* No resource is allocated to multiple clients
AllocatedMutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => allocated[c1] \cap allocated[c2] = {}

\* Held and allocated resources don't overlap
HeldAllocatedDisjoint ==
    \A c1, c2 \in Clients : holding[c1] \cap allocated[c2] = {}

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ MutualExclusion
    /\ NoHoldingEarlierRequested
    /\ ScheduleConsistency
    /\ AllocationConsistency
    /\ AllocatedMutualExclusion
    /\ HeldAllocatedDisjoint

-----------------------------------------------------------------------------
(* Allocation feasibility *)

\* For every scheduled client, every remaining requested resource is reachable
\* assuming earlier scheduled clients eventually release what they hold
AllocationFeasibility ==
    \A c \in ScheduledClients :
        RemainingRequests(c) \subseteq 
            (AvailableResources \cup EarlierHeldResources(c) \cup 
             UNION {allocated[c2] : c2 \in EarlierClients(c)})

-----------------------------------------------------------------------------
(* Fairness conditions *)

\* Clients eventually return resources after request is fully satisfied
ClientReturnFairness ==
    \A c \in Clients :
        WF_vars(Return(c))

\* Allocator eventually allocates when possible
AllocatorProgressFairness ==
    \A c \in Clients :
        WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

\* Clients eventually receive their allocations
ReceiveFairness ==
    \A c \in Clients :
        WF_vars(ReceiveAllocation(c))

\* Allocator eventually schedules requesting clients
SchedulingFairness ==
    WF_vars(Schedule)

\* Combined fairness
Fairness ==
    /\ ClientReturnFairness
    /\ AllocatorProgressFairness
    /\ ReceiveFairness
    /\ SchedulingFairness

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every requested resource is eventually allocated to the requesting client
EventualAllocation ==
    \A c \in Clients : \A r \in Resources :
        (r \in requests[c]) ~> (r \in holding[c])

\* Each client's requests are satisfied infinitely often
\* (if a client makes a request, it will eventually be fully satisfied)
RequestEventuallySatisfied ==
    \A c \in Clients :
        (requests[c] /= {}) ~> (requests[c] \subseteq holding[c])

\* Every requesting client is eventually scheduled
EventuallyScheduled ==
    \A c \in Clients :
        (requests[c] /= {} /\ c \notin ScheduledClients) ~> (c \in ScheduledClients)

\* Combined liveness
Liveness ==
    /\ EventualAllocation
    /\ RequestEventuallySatisfied
    /\ EventuallyScheduled

-----------------------------------------------------------------------------
(* Specification *)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-----------------------------------------------------------------------------
(* Theorems to verify *)

THEOREM Spec => []Safety
THEOREM Spec => []AllocationFeasibility
THEOREM Spec => Liveness

=============================================================================