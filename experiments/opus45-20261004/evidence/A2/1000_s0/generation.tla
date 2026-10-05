---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS FiniteSets

CONSTANTS
    Clients,    \* The set of all clients
    Resources   \* The set of all resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc       \* alloc[c] = set of resources currently allocated to client c

vars == <<unsat, alloc>>

-----------------------------------------------------------------------------
(* Type definitions and helper operators *)

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(* The set of resources currently allocated to some client *)
Allocated == UNION {alloc[c] : c \in Clients}

(* The set of resources that are currently available (not allocated) *)
Available == Resources \ Allocated

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

-----------------------------------------------------------------------------
(* Actions *)

(* Client c requests a nonempty set S of resources.
   Only allowed when c holds no resources and has no pending request. *)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ alloc[c] = {}
    /\ unsat[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(* Allocator grants a nonempty subset S of available resources to client c,
   where S must overlap with c's outstanding request. *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq Available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a nonempty subset S of its currently held resources. *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ \E S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Fairness conditions *)

(* Full return: client returns all its resources *)
FullReturn(c) == Return(c, alloc[c])

(* Weak fairness on full returns for all clients *)
FairnessReturn == \A c \in Clients : WF_vars(FullReturn(c))

(* Strong fairness on allocations for all clients *)
FairnessAllocate == \A c \in Clients : \E S \in SUBSET Resources : SF_vars(Allocate(c, S))

(* Alternative: Strong fairness on any allocation action *)
FairnessAllocateAlt == \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

-----------------------------------------------------------------------------
(* Return only after full request is satisfied *)
FullReturnAfterSatisfied(c) == 
    /\ unsat[c] = {}
    /\ alloc[c] # {}
    /\ Return(c, alloc[c])

FairnessReturn2 == \A c \in Clients : WF_vars(FullReturnAfterSatisfied(c))

-----------------------------------------------------------------------------
(* Specifications *)

SimpleAllocator ==
    /\ Init
    /\ [][Next]_vars
    /\ FairnessReturn
    /\ FairnessAllocateAlt

SimpleAllocator2 ==
    /\ Init
    /\ [][Next]_vars
    /\ FairnessReturn2
    /\ FairnessAllocateAlt

Spec == SimpleAllocator

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* No two clients hold the same resource simultaneously *)
ResourceMutex ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* A client is satisfied when its outstanding request is empty *)
Satisfied(c) == unsat[c] = {}

(* Clients eventually release resources once satisfied *)
ClientsWillReturn ==
    \A c \in Clients : (Satisfied(c) /\ alloc[c] # {}) ~> alloc[c] = {}

(* Every requested resource is eventually allocated *)
ClientsWillObtain ==
    \A c \in Clients : \A r \in Resources : r \in unsat[c] ~> r \in alloc[c]

(* Every client is satisfied infinitely often *)
InfOftenSatisfied ==
    \A c \in Clients : []<>Satisfied(c)

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied

THEOREM SimpleAllocator2 => []TypeInvariant
THEOREM SimpleAllocator2 => []ResourceMutex
THEOREM SimpleAllocator2 => ClientsWillReturn
(* Note: SimpleAllocator2 does NOT guarantee ClientsWillObtain or InfOftenSatisfied *)

=============================================================================