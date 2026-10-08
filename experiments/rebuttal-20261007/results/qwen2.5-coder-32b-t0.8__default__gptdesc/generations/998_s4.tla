---- MODULE ResourceAllocator ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Clients,                \* The set of clients
    Resources               \* The set of resources

VARIABLES 
    clientRequests,         \* Maps each client to a request (set of resources)
    allocations,            \* Maps each resource to the client that holds it
    scheduleSequence        \* A sequence of clients representing the order of requests to be served

Init == 
    /\ clientRequests = [c \in Clients |-> {}]
    /\ allocations = [r \in Resources |-> <<>>]
    /\ scheduleSequence = <<>>

Next ==
    \/ \E c \in Clients, r \in Resources :
        /\ clientRequests[c] # {}
        /\ allocations[r] = <<>>
        /\ scheduleSequence # <<>> 
        /\ Head(scheduleSequence) = c
        /\ scheduleSequence' = Tail(scheduleSequence)
        /\ allocations' = [allocations EXCEPT ![r] = <<c>>]
    \/ \E c \in Clients, r \in Resources :
        /\ allocations[r] = <<c>>
        /\ c \notin {c' \in Clients | clientRequests[c'] # {}}
        /\ allocations' = [allocations EXCEPT ![r] = <<>>]
    \/ \E c \in Clients :
        /\ clientRequests[c] = {}
        /\ allocations' = allocations
        /\ scheduleSequence' = Append(scheduleSequence, <<c>>)
    \/ \E c \in Clients, rs \in Subsets(Resources) :
        /\ clientRequests[c] = rs
        /\ allocations' = allocations
        /\ clientRequests' = [clientRequests EXCEPT ![c] = {}]
        /\ scheduleSequence' = scheduleSequence

Spec == 
    /\ Init
    /\ [][Next]_<<clientRequests, allocations, scheduleSequence>>

\* Type invariants
TypeOK ==
    /\ clientRequests \in [Clients -> SUBSET Resources]
    /\ allocations \in [Resources -> <<CLIENTS>>]
    /\ scheduleSequence \in Seq(Clients)

\* Mutual exclusion invariant
MutualExclusion ==
    \A r \in Resources : Len(allocations[r]) <= 1

\* Allocator invariants
AllocatorInvariant ==
    TypeOK /\ MutualExclusion

\* Liveness properties
EventualReturn ==
    \A c \in Clients :
        WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
        -> []<>(\E r \in Resources : allocations[r] = <<c>>)

EventualObtainment ==
    \A c \in Clients :
        \A rs \in SUBSET Resources :
            WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
            -> clientRequests[c] = rs /\ []<>(allocations' = [r \in Resources |-> IF r \in rs THEN <<c>> ELSE allocations[r]])

InfinitelyOftenSatisfied ==
    \A c \in Clients :
        WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
        -> []<>(\E r \in Resources : allocations[r] = <<c>>) => <>(allocations' = [r \in Resources |-> IF r \in clientRequests[c] THEN <<>> ELSE allocations[r]])

\* Fairness assumptions
FairReturn ==
    \A c \in Clients, rs \in SUBSET Resources :
        WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
        -> [](allocations' = [r \in Resources |-> IF r \in rs THEN <<c>> ELSE allocations[r]]) ~> <>(allocations' = [r \in Resources |-> IF r \in rs THEN <<>> ELSE allocations[r]])

FairAllocation ==
    \A c \in Clients, rs \in SUBSET Resources :
        WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
        -> [](clientRequests[c] = rs /\ allocations' = allocations) ~> <>(allocations' = [r \in Resources |-> IF r \in rs THEN <<c>> ELSE allocations[r]])

FairScheduling ==
    \A c \in Clients :
        WF_(Next)_<<clientRequests, allocations, scheduleSequence>>
        -> [](scheduleSequence' = Append(scheduleSequence, <<c>>)) ~> <>(scheduleSequence' = Tail(scheduleSequence))

====