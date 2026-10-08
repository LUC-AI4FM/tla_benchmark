---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Clients,      \* Set of all clients
    Resources     \* Set of all resources

VARIABLES
    requests,     \* requests[c] = set of resources requested by client c (empty if none)
    holding,      \* holding[c] = set of resources currently held by client c
    schedule      \* Sequence of clients with outstanding requests

vars == <<requests, holding, schedule>>

----------------------------------------------------------------------------
\* Helper functions

\* Set of all resources currently held by any client
AllocatedResources == UNION {holding[c] : c \in Clients}

\* Available resources (not held by anyone)
AvailableResources == Resources \ AllocatedResources

\* Resources still needed by client c (requested but not yet held)
Unmet(c) == requests[c] \ holding[c]

\* Clients with outstanding requests (requested something they don't have yet)
ClientsWithOutstandingRequests == {c \in Clients : requests[c] # {} /\ Unmet(c) # {}}

\* Clients in the schedule (as a set)
ScheduledClients == {schedule[i] : i \in 1..Len(schedule)}

\* Unscheduled clients with pending requests
UnscheduledWithRequests == ClientsWithOutstandingRequests \ ScheduledClients

\* Resources requested by clients appearing before position i in schedule
ResourcesRequestedBefore(i) ==
    IF i <= 1 THEN {}
    ELSE UNION {requests[schedule[j]] : j \in 1..(i-1)}

\* Position of client c in schedule (0 if not in schedule)
PositionInSchedule(c) ==
    IF c \in ScheduledClients
    THEN CHOOSE i \in 1..Len(schedule) : schedule[i] = c
    ELSE 0

\* Check if resource r can be allocated to client c
\* (no earlier scheduled client has requested r)
CanAllocate(c, r) ==
    /\ c \in ScheduledClients
    /\ r \in AvailableResources
    /\ r \in Unmet(c)
    /\ LET pos == PositionInSchedule(c)
       IN r \notin ResourcesRequestedBefore(pos)

\* All permutations of a set as sequences
PermSeqs(S) ==
    IF S = {} THEN {<<>>}
    ELSE {<<s>> \o rest : s \in S, rest \in PermSeqs(S \ {s})}

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ holding = [c \in Clients |-> {}]
    /\ schedule = <<>>

----------------------------------------------------------------------------
\* Actions

\* Client c requests a non-empty set of resources S
\* Precondition: c has no outstanding request and holds no resources
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ requests[c] = {}
    /\ holding[c] = {}
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<holding, schedule>>

\* Allocator allocates resource r to client c
Allocate(c, r) ==
    /\ CanAllocate(c, r)
    /\ holding' = [holding EXCEPT ![c] = @ \cup {r}]
    /\ UNCHANGED <<requests, schedule>>

\* Client c returns a non-empty subset S of held resources
\* Client may return resources at any time while holding them
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq holding[c]
    /\ holding' = [holding EXCEPT ![c] = @ \ S]
    \* If client has returned all resources and request was fully met, clear request
    /\ IF holding[c] \ S = {} /\ requests[c] \subseteq holding[c]
       THEN requests' = [requests EXCEPT ![c] = {}]
       ELSE requests' = requests
    \* Remove from schedule if no longer has outstanding request
    /\ LET newRequests == IF holding[c] \ S = {} /\ requests[c] \subseteq holding[c]
                          THEN {}
                          ELSE requests[c]
           newUnmet == newRequests \ (holding[c] \ S)
           stillOutstanding == newRequests # {} /\ newUnmet # {}
       IN IF ~stillOutstanding /\ c \in ScheduledClients
          THEN schedule' = SelectSeq(schedule, LAMBDA x: x # c)
          ELSE schedule' = schedule

\* Client c releases all resources after being fully satisfied
\* This is the obligated return once full request is granted
ReleaseAll(c) ==
    /\ holding[c] # {}
    /\ requests[c] \subseteq holding[c]  \* fully satisfied
    /\ holding' = [holding EXCEPT ![c] = {}]
    /\ requests' = [requests EXCEPT ![c] = {}]
    /\ IF c \in ScheduledClients
       THEN schedule' = SelectSeq(schedule, LAMBDA x: x # c)
       ELSE schedule' = schedule

\* Allocator extends schedule by appending a permutation of unscheduled clients with requests
ExtendSchedule ==
    /\ UnscheduledWithRequests # {}
    /\ \E perm \in PermSeqs(UnscheduledWithRequests):
         schedule' = schedule \o perm
    /\ UNCHANGED <<requests, holding>>

----------------------------------------------------------------------------
\* Next state relation

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, r \in Resources : Allocate(c, r)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)
    \/ \E c \in Clients : ReleaseAll(c)
    \/ ExtendSchedule

----------------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Safety Invariants

\* Type invariant
TypeInvariant ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ holding \in [Clients -> SUBSET Resources]
    /\ schedule \in Seq(Clients)

\* Resources are allocated exclusively (no resource held by two clients)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => holding[c1] \cap holding[c2] = {}

\* All clients in schedule have outstanding requests
ScheduleValid ==
    \A i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN requests[c] # {} /\ Unmet(c) # {}

\* No duplicates in schedule
ScheduleNoDuplicates ==
    \A i, j \in 1..Len(schedule) : i # j => schedule[i] # schedule[j]

\* The allocator can satisfy each scheduled client assuming earlier ones release
\* This means: for each scheduled client, their requested resources exist and
\* are either available, held by themselves, or held by earlier scheduled clients
ResourcesExist ==
    \A i \in 1..Len(schedule) :
        LET c == schedule[i]
            earlierClients == {schedule[j] : j \in 1..(i-1)}
            resourcesHeldByEarlierOrSelf == UNION {holding[d] : d \in earlierClients \cup {c}}
        IN requests[c] \subseteq (AvailableResources \cup resourcesHeldByEarlierOrSelf \cup holding[c])

\* Combined safety invariant
Safety ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ ScheduleValid
    /\ ScheduleNoDuplicates

----------------------------------------------------------------------------
\* Fairness Conditions

\* Allocator eventually schedules pending clients
SchedulingFairness ==
    WF_vars(ExtendSchedule)

\* Allocator eventually allocates available resources
AllocationFairness ==
    \A c \in Clients, r \in Resources :
        WF_vars(Allocate(c, r))

\* Clients eventually return all resources once fully satisfied
ReturnFairness ==
    \A c \in Clients :
        WF_vars(ReleaseAll(c))

FairSpec == Spec /\ SchedulingFairness /\ AllocationFairness /\ ReturnFairness

----------------------------------------------------------------------------
\* Liveness Properties

\* A client is fully satisfied when they hold all requested resources
FullySatisfied(c) == requests[c] # {} /\ requests[c] \subseteq holding[c]

\* Every client eventually obtains each requested resource
EventuallyGetResources ==
    \A c \in Clients, r \in Resources :
        [](r \in requests[c] => <>(r \in holding[c]))

\* Every satisfied client eventually releases all resources
EventuallyRelease ==
    \A c \in Clients :
        [](FullySatisfied(c) => <>(holding[c] = {}))

\* Every client is fully satisfied infinitely often
\* (either they make no request, or they get satisfied)
InfinitelyOftenSatisfied ==
    \A c \in Clients :
        []<>(requests[c] = {} \/ FullySatisfied(c))

\* Combined liveness
Liveness ==
    /\ EventuallyGetResources
    /\ EventuallyRelease
    /\ InfinitelyOftenSatisfied

============================================================================