---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Clients,        \* The set of clients
    Resources       \* The set of resources

VARIABLES
    requests,       \* requests[c] = set of resources client c is requesting (empty if no outstanding request)
    allocated,      \* allocated[c] = set of resources currently held by client c
    available       \* set of resources currently available in the pool

vars == <<requests, allocated, available>>

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ allocated \in [Clients -> SUBSET Resources]
    /\ available \subseteq Resources

-----------------------------------------------------------------------------
Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ allocated = [c \in Clients |-> {}]
    /\ available = Resources

-----------------------------------------------------------------------------
\* A client submits a request for a nonempty set of resources
\* Precondition: client has no outstanding request and holds no resources
Request(c, S) ==
    /\ S # {}                           \* Request must be nonempty
    /\ S \subseteq Resources            \* Request valid resources
    /\ requests[c] = {}                 \* No outstanding request
    /\ allocated[c] = {}                \* Holds no resources
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<allocated, available>>

\* The allocator allocates a nonempty subset of requested resources that are available
\* This can be a partial allocation
Allocate(c, S) ==
    /\ S # {}                           \* Must allocate something
    /\ S \subseteq requests[c]          \* Can only allocate requested resources
    /\ S \subseteq available            \* Resources must be available
    /\ allocated' = [allocated EXCEPT ![c] = @ \cup S]
    /\ requests' = [requests EXCEPT ![c] = @ \ S]
    /\ available' = available \ S

\* A client returns some subset of its held resources
\* Can return any nonempty subset at any time
Return(c, S) ==
    /\ S # {}                           \* Must return something
    /\ S \subseteq allocated[c]         \* Can only return held resources
    /\ allocated' = [allocated EXCEPT ![c] = @ \ S]
    /\ available' = available \cup S
    /\ UNCHANGED requests

\* A client returns ALL its resources (used for fairness - obligated when fully satisfied)
ReturnAll(c) ==
    /\ requests[c] = {}                 \* Request fully satisfied (no outstanding request)
    /\ allocated[c] # {}                \* Has resources to return
    /\ allocated' = [allocated EXCEPT ![c] = {}]
    /\ available' = available \cup allocated[c]
    /\ UNCHANGED requests

-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
\* Fairness conditions

\* Strong fairness for allocation: if allocation is repeatedly enabled, it eventually happens
\* For each client and each possible nonempty subset of their request that could be allocated
AllocateFairness ==
    \A c \in Clients : \A S \in SUBSET Resources :
        SF_vars(Allocate(c, S))

\* Weak fairness for returning all resources once fully satisfied
\* A client is obligated to return resources once its entire request has been fulfilled
ReturnAllFairness ==
    \A c \in Clients : WF_vars(ReturnAll(c))

Fairness == AllocateFairness /\ ReturnAllFairness

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety Properties

\* Mutual Exclusion: no resource is ever held by more than one client simultaneously
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => allocated[c1] \cap allocated[c2] = {}

\* All resources are accounted for (either available or allocated to exactly one client)
ResourcesAccountedFor ==
    available \cup UNION {allocated[c] : c \in Clients} = Resources

\* Safety invariant combining all safety properties
SafetyInvariant == TypeInvariant /\ MutualExclusion /\ ResourcesAccountedFor

-----------------------------------------------------------------------------
\* Liveness Properties

\* Eventual Return: whenever a client has no outstanding requests, it will eventually release all held resources
EventualReturn ==
    \A c \in Clients : (requests[c] = {} /\ allocated[c] # {}) ~> (allocated[c] = {})

\* Eventual Allocation: every resource in an outstanding request will eventually be allocated to that client
\* For each resource in a request, it will eventually be allocated
EventualAllocation ==
    \A c \in Clients : \A r \in Resources :
        (r \in requests[c]) ~> (r \in allocated[c])

\* Helper: client c is fully satisfied (no outstanding request and we consider the moment after getting all requested)
FullySatisfied(c) == requests[c] = {}

\* Infinite Satisfiability: every client's outstanding request is eventually fully satisfied infinitely often
\* This means: it's always the case that a client will eventually be in a fully satisfied state
InfiniteSatisfiability ==
    \A c \in Clients : []<>(requests[c] = {} /\ allocated[c] = {})

-----------------------------------------------------------------------------
\* Combined liveness property
LivenessProperty == EventualReturn /\ EventualAllocation /\ InfiniteSatisfiability

=============================================================================