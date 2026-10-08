---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Resources,      \* The fixed finite set of resources
    Clients         \* The fixed finite set of clients

VARIABLES
    holding,        \* holding[c] = set of resources currently held by client c
    request,        \* request[c] = set of resources currently requested by client c (outstanding request)
    allocated       \* allocated = set of all resources currently allocated to some client

-----------------------------------------------------------------------------
(* Type definitions and type invariant *)

TypeOK ==
    /\ holding \in [Clients -> SUBSET Resources]
    /\ request \in [Clients -> SUBSET Resources]
    /\ allocated \in SUBSET Resources

-----------------------------------------------------------------------------
(* Derived definitions *)

\* The set of resources currently free (not allocated to any client)
Free == Resources \ allocated

\* A client is idle if it holds no resources and has no outstanding request
Idle(c) == holding[c] = {} /\ request[c] = {}

\* A client has been fully satisfied when its request becomes empty
\* (but it may still be holding resources that were granted)
FullySatisfied(c) == request[c] = {} /\ holding[c] /= {}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ holding = [c \in Clients |-> {}]
    /\ request = [c \in Clients |-> {}]
    /\ allocated = {}

-----------------------------------------------------------------------------
(* Actions *)

\* Client c issues a new request for a nonempty set of resources S
\* Precondition: client must be idle (no resources held, no outstanding request)
Request(c, S) ==
    /\ Idle(c)
    /\ S /= {}
    /\ S \subseteq Resources
    /\ request' = [request EXCEPT ![c] = S]
    /\ UNCHANGED <<holding, allocated>>

\* Allocator grants a nonempty subset S of requested resources to client c
\* S must be free and part of c's outstanding request
Grant(c, S) ==
    /\ S /= {}
    /\ S \subseteq request[c]
    /\ S \subseteq Free
    /\ holding' = [holding EXCEPT ![c] = @ \cup S]
    /\ request' = [request EXCEPT ![c] = @ \ S]
    /\ allocated' = allocated \cup S

\* Client c returns a nonempty subset S of resources it currently holds
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq holding[c]
    /\ holding' = [holding EXCEPT ![c] = @ \ S]
    /\ allocated' = allocated \ S
    /\ UNCHANGED <<request>>

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Grant(c, S)
        \/ \E S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Exclusivity: no resource is allocated to more than one client
\* This is implied by the design but we state it explicitly
Exclusivity ==
    \A c1, c2 \in Clients :
        c1 /= c2 => holding[c1] \cap holding[c2] = {}

\* The allocated set correctly reflects what clients are holding
AllocatedConsistent ==
    allocated = UNION {holding[c] : c \in Clients}

\* Requests are always subsets of resources (well-formed)
RequestsWellFormed ==
    \A c \in Clients : request[c] \subseteq Resources

\* Holdings are always subsets of resources (well-formed)
HoldingsWellFormed ==
    \A c \in Clients : holding[c] \subseteq Resources

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ Exclusivity
    /\ AllocatedConsistent
    /\ RequestsWellFormed
    /\ HoldingsWellFormed

-----------------------------------------------------------------------------
(* Fairness Conditions *)

\* Weak fairness on Grant actions: if granting is continuously enabled, it eventually happens
\* This ensures the allocator will eventually grant available resources
FairGrant ==
    \A c \in Clients : \A S \in SUBSET Resources :
        WF_<<holding, request, allocated>>(Grant(c, S))

\* Weak fairness on Return actions: if returning is continuously enabled, it eventually happens
\* This ensures clients will eventually return resources
FairReturn ==
    \A c \in Clients : \A S \in SUBSET Resources :
        WF_<<holding, request, allocated>>(Return(c, S))

\* Strong fairness on Grant: if granting is repeatedly enabled, it eventually happens
\* This is needed because resources may become available repeatedly but not continuously
StrongFairGrant ==
    \A c \in Clients : \A S \in SUBSET Resources :
        SF_<<holding, request, allocated>>(Grant(c, S))

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Eventual allocation: if a client requests a resource, it will eventually be granted
\* (the resource will eventually leave the request set)
EventualAllocation ==
    \A c \in Clients : \A r \in Resources :
        (r \in request[c]) ~> (r \notin request[c])

\* Eventual return: once a client's request is fully satisfied (request empty, holding nonempty),
\* the client must eventually return all resources
EventualReturn ==
    \A c \in Clients :
        (request[c] = {} /\ holding[c] /= {}) ~> (holding[c] = {})

\* Repeated satisfaction: each client's request is satisfied infinitely often
\* (equivalently, each client reaches a state with no outstanding request infinitely often)
RepeatedSatisfaction ==
    \A c \in Clients : []<>(request[c] = {})

\* Combined liveness property
LivenessProperty ==
    /\ EventualAllocation
    /\ EventualReturn
    /\ RepeatedSatisfaction

-----------------------------------------------------------------------------
(* Specification *)

\* The full specification with fairness conditions
Spec ==
    /\ Init
    /\ [][Next]_<<holding, request, allocated>>
    /\ StrongFairGrant
    /\ FairReturn

-----------------------------------------------------------------------------
(* Theorems to verify *)

THEOREM Spec => []SafetyInvariant

THEOREM Spec => LivenessProperty

=============================================================================