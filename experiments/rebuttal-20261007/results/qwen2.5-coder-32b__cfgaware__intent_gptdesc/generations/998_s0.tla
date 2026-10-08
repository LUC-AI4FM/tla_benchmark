------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Clients,                      \* Finite set of clients
    Resources                     \* Finite set of resources

VARIABLES 
    heldResources,                \* Function from clients to sets of resources they hold
    requestedResources,           \* Function from clients to sets of resources they request
    schedule                      \* Ordered list of scheduled clients with outstanding requests

ASSUME 
    FINITE Clients /\ FINITE Resources

CONSTANTS Init

Init == 
    /\ heldResources = [c \in Clients |-> {}]
    /\ requestedResources = [c \in Clients |-> {}]
    /\ schedule = <<>>

VARIABLES pc

Next ==
    \/ \E c \in Clients, r \subseteq Resources \: Request(c, r)
    \/ \E c \in Clients, r \subseteq (heldResources[c]) \: Return(c, r)
    \/ Allocate
    \/ ExtendSchedule

Request(c, r) ==
    /\ requestedResources' = [requestedResources EXCEPT ![c] = r]
    /\ heldResources' = heldResources
    /\ schedule' = Append(schedule, <<c>>)

Return(c, r) ==
    /\ \A c' \in Clients : heldResources'[c'] = 
        IF c' = c THEN (heldResources[c] \ r)
        ELSE heldResources[c']
    /\ requestedResources' = [requestedResources EXCEPT ![c] = {}]
    /\ schedule' = Remove(schedule, c)

Allocate ==
    /\ \E i \in 1..Len(schedule) : 
        LET c == schedule[i]
            available == Resources \ (UNION {heldResources[c'] | c' \in Take(schedule, i-1)})
            allocatable == requestedResources[c] \cap available
        IN
        \/ allocatable = {}
        \/ \E r \subseteq allocatable, r /= {} :
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup r]
            /\ requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \ r]
            /\ schedule' = schedule

ExtendSchedule ==
    /\ \E perm \in Permutations({c \in Clients | requestedResources[c] /= {}}) :
        schedule' = Append(schedule, <<perm>>)
    /\ heldResources' = heldResources
    /\ requestedResources' = requestedResources

Spec == 
    Init /\ [][Next]_<<pc>>

MutualExclusion ==
    \A r \in Resources : Cardinality({c \in Clients | r \in heldResources[c]}) <= 1

NoEarlyAllocation ==
    \A i, j \in 1..Len(schedule) : i < j => 
        requestedResources[schedule[i]] \cap (UNION {heldResources[c] | c \in Take(schedule, j-1)}) = {}

ScheduledRequests ==
    \A c \in Clients : c \in schedule => requestedResources[c] /= {}

AllocationFeasibility ==
    \A i \in 1..Len(schedule) :
        LET c == schedule[i]
            remaining == requestedResources[c]
            available == Resources \ (UNION {heldResources[c'] | c' \in Take(schedule, i-1)})
        IN
        remaining \subseteq available \/ 
        (\E perm \in Permutations({c' \in Clients | c' /= c}) :
            \A j \in 1..Len(perm) :
                LET c'' == perm[j]
                    allocatable == requestedResources[c''] \cap (available \ (UNION {heldResources[c''']} | c''' \in Take(perm, j-1)))
                IN
                allocatable /= {})

ClientProgress ==
    \A c \in Clients : WF_pc(\E r \subseteq Resources : Request(c, r) /\ requestedResources'[c] = r)

AllocatorProgress ==
    \A i \in 1..Len(schedule) :
        LET c == schedule[i]
            available == Resources \ (UNION {heldResources[c'] | c' \in Take(schedule, i-1)})
            allocatable == requestedResources[c] \cap available
        IN
        WF_pc(allocatable /= {})

ScheduleProgress ==
    \A c \in Clients : requestedResources[c] /= {} => WF_pc(c \in schedule)

ResourceAllocation ==
    \A r \in Resources :
        WF_pc(\E c \in Clients : r \in heldResources[c])

RequestSatisfaction ==
    \A c \in Clients : WF_pc(requestedResources[c] = {})

THEOREM Spec => []MutualExclusion
THEOREM Spec => []NoEarlyAllocation
THEOREM Spec => []ScheduledRequests
THEOREM Spec => []AllocationFeasibility
THEOREM Spec => <>[]ClientProgress
THEOREM Spec => <>[]AllocatorProgress
THEOREM Spec => <>[]ScheduleProgress
THEOREM Spec => <>[]ResourceAllocation
THEOREM Spec => <>[]RequestSatisfaction

=============================================================================