---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    requests,    \* requests[c] = set of resources client c is requesting
    allocated,   \* allocated[c] = set of resources currently held by client c
    available    \* set of resources not held by any client

vars == <<requests, allocated, available>>

TypeInvariant ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ allocated \in [Clients -> SUBSET Resources]
    /\ available \subseteq Resources

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ allocated = [c \in Clients |-> {}]
    /\ available = Resources

-----------------------------------------------------------------------------
(* Client c submits a request for a nonempty set S of resources.
   Precondition: c has no outstanding request and holds no resources. *)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ requests[c] = {}
    /\ allocated[c] = {}
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<allocated, available>>

(* Allocator allocates a nonempty subset S of requested resources to client c.
   S must be available and part of c's outstanding request. *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq requests[c]
    /\ S \subseteq available
    /\ allocated' = [allocated EXCEPT ![c] = @ \cup S]
    /\ requests' = [requests EXCEPT ![c] = @ \ S]
    /\ available' = available \ S

(* Client c returns a nonempty subset S of its held resources. *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq allocated[c]
    /\ allocated' = [allocated EXCEPT ![c] = @ \ S]
    /\ available' = available \cup S
    /\ UNCHANGED requests

(* Client c returns all its held resources when fully satisfied (no outstanding request). *)
ReturnAll(c) ==
    /\ requests[c] = {}
    /\ allocated[c] # {}
    /\ allocated' = [allocated EXCEPT ![c] = {}]
    /\ available' = available \cup allocated[c]
    /\ UNCHANGED requests

-----------------------------------------------------------------------------
(* Next state relation *)
Next ==
    \/ \E c \in Clients : \E S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients : \E S \in SUBSET Resources : Return(c, S)
    \/ \E c \in Clients : ReturnAll(c)

-----------------------------------------------------------------------------
(* Fairness conditions *)

(* Strong fairness on allocation actions - if allocation is repeatedly enabled, it eventually happens *)
AllocateFairness ==
    \A c \in Clients : \A S \in SUBSET Resources :
        SF_vars(Allocate(c, S))

(* Weak fairness on returning all resources once fully satisfied *)
ReturnAllFairness ==
    \A c \in Clients : WF_vars(ReturnAll(c))

Fairness == AllocateFairness /\ ReturnAllFairness

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

(* Mutual exclusion: no resource is held by more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => allocated[c1] \cap allocated[c2] = {}

(* All allocated resources are accounted for *)
ResourceIntegrity ==
    available = Resources \ UNION {allocated[c] : c \in Clients}

Safety == MutualExclusion /\ ResourceIntegrity

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Eventual return: if a client has no outstanding requests, it will eventually release all resources *)
EventualReturn ==
    \A c \in Clients : (requests[c] = {} /\ allocated[c] # {}) ~> (allocated[c] = {})

(* Eventual allocation: every resource in an outstanding request will eventually be allocated *)
EventualAllocation ==
    \A c \in Clients : \A r \in Resources :
        (r \in requests[c]) ~> (r \in allocated[c])

(* Infinite satisfiability: every client's request is fully satisfied infinitely often *)
InfiniteSatisfiability ==
    \A c \in Clients : []<>(requests[c] = {})

Liveness == EventualReturn /\ EventualAllocation /\ InfiniteSatisfiability

=============================================================================