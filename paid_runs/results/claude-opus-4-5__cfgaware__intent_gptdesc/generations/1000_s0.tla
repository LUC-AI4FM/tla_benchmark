---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    request,    \* request[c] = set of resources client c is currently requesting
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    holding     \* holding[c] = set of resources client c currently holds

vars == <<request, alloc, holding>>

-----------------------------------------------------------------------------
(* Type invariant: all state variables are mappings from clients to subsets of resources *)

TypeOK ==
    /\ request \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ holding \in [Clients -> SUBSET Resources]

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Set of all resources currently held by any client
UsedResources == UNION {holding[c] : c \in Clients}

\* Set of all resources that are free (not held by anyone)
FreeResources == Resources \ UsedResources

\* A client can make a request only if it holds nothing and has no outstanding request
CanRequest(c) == holding[c] = {} /\ request[c] = {}

\* A client has an outstanding request
HasRequest(c) == request[c] /= {}

\* Resources that can be granted to client c: must be free, requested, and not yet allocated
GrantableResources(c) == request[c] \cap FreeResources

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ request = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ holding = [c \in Clients |-> {}]

-----------------------------------------------------------------------------
(* Actions *)

\* Client c requests a nonempty set S of resources
Request(c, S) ==
    /\ CanRequest(c)
    /\ S /= {}
    /\ S \subseteq Resources
    /\ request' = [request EXCEPT ![c] = S]
    /\ UNCHANGED <<alloc, holding>>

\* Allocator grants a nonempty subset S of grantable resources to client c
Allocate(c, S) ==
    /\ S /= {}
    /\ S \subseteq GrantableResources(c)
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ holding' = [holding EXCEPT ![c] = holding[c] \cup S]
    /\ request' = [request EXCEPT ![c] = request[c] \ S]

\* Client c returns a nonempty subset S of resources it currently holds
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq holding[c]
    /\ holding' = [holding EXCEPT ![c] = holding[c] \ S]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED <<request>>

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \/ \E c \in Clients : \E S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Fairness conditions *)

\* Weak fairness on allocation: if resources can be granted, they eventually will be
AllocatorFairness ==
    \A c \in Clients : \A r \in Resources :
        WF_vars(Allocate(c, {r}))

\* Weak fairness on return: if a client's request is satisfied and it holds resources,
\* it will eventually return them
ReturnFairness ==
    \A c \in Clients : \A S \in SUBSET Resources :
        WF_vars(Return(c, S))

Fairness == AllocatorFairness /\ ReturnFairness

-----------------------------------------------------------------------------
(* Complete specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Exclusivity: no resource is allocated to more than one client simultaneously
Exclusivity ==
    \A c1, c2 \in Clients :
        c1 /= c2 => holding[c1] \cap holding[c2] = {}

\* Safety property combining type correctness and exclusivity
Safety == TypeOK /\ Exclusivity

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* If a client has an outstanding request, every requested resource will eventually be granted
\* (the request will eventually become empty)
EventualAllocation ==
    \A c \in Clients :
        HasRequest(c) ~> (request[c] = {})

\* Once a client's request is fully satisfied (request empty), it will eventually return all resources
EventualReturn ==
    \A c \in Clients :
        (request[c] = {} /\ holding[c] /= {}) ~> (holding[c] = {})

\* Every client repeatedly reaches states with no outstanding request
RepeatedSatisfaction ==
    \A c \in Clients :
        []<>(request[c] = {})

\* Combined liveness property
Liveness == EventualAllocation /\ EventualReturn /\ RepeatedSatisfaction

-----------------------------------------------------------------------------
(* System goal: Safety and Liveness *)

SystemGoal == Safety /\ Liveness

=============================================================================