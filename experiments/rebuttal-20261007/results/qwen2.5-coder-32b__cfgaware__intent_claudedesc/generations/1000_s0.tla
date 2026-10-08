------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Clients,                \* The set of all clients
    Resources               \* The set of all resources

VARIABLES 
    requests,               \* A function mapping each client to a nonempty set of requested resources (or the empty set if no request)
    allocations             \* A function mapping each resource to a client (or << >> if unallocated)

ASSUME
    Clients /= {} /\ Resources /= {}
    \A c \in Clients: requests[c] \subseteq Resources
    \A r \in Resources: allocations[r] \in Clients \/ allocations[r] = << >>

CONSTANTS 
    Init,                   \* The initial predicate
    Next,                   \* The next-state action
    Spec                    \* The complete specification

Init == 
    /\ requests = [c \in Clients |-> {}]
    /\ allocations = [r \in Resources |-> << >>]

Next ==
    \/ \E c \in Clients, rs \subseteq Resources \: rs /= {} /\ requests[c] = {} /\ (\A r \in rs: allocations[r] = << >>)
        /\ requests' = [requests EXCEPT ![c] = rs]
        /\ allocations' = allocations
    \/ \E c \in Clients, rs \subseteq Resources \: rs /= {} /\ requests[c] = rs
        /\ \E r \in rs: allocations[r] = << >>
        /\ \E r \in rs: allocations'[r] = c
        /\ requests' = requests
        /\ allocations'' = [allocations EXCEPT ![r] = c]
    \/ \E c \in Clients, rs \subseteq Resources \: rs /= {} /\ (\A r \in rs: allocations[r] = c)
        /\ requests'[c] = {}
        /\ allocations'' = [allocations EXCEPT !>> r \in rs: << >>]

Spec ==
    WF_vars(Next, <<requests, allocations>>) /\
    SF_vars(Next, <<requests, allocations>>) /\
    WF_vars(ReturnFullAllocation, <<requests, allocations>>) /\
    Spec_Theorem

MutualExclusion ==
    \A r \in Resources: Cardinality({c \in Clients: allocations[r] = c}) <= 1

EventualReturn ==
    \A c \in Clients: 
        <>[] (requests[c] = {} /\ (\A r \in Resources: allocations[r] # c))

EventualAllocation ==
    \A c \in Clients, rs \subseteq Resources:
        requests[c] = rs
        -> <>(\A r \in rs: allocations[r] = c)

InfiniteSatisfiability ==
    \A c \in Clients, rs \subseteq Resources:
        requests[c] = rs
        -> []<>(requests[c] = {} /\ (\A r \in rs: allocations[r] # c))

ReturnFullAllocation ==
    {c \in Clients: requests[c] = {}}

Spec_Theorem ==
    MutualExclusion /\ EventualReturn /\ EventualAllocation /\ InfiniteSatisfiability

=============================================================================