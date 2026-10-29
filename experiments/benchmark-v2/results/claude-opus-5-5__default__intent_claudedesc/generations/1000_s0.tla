-------------------------- MODULE SimpleAllocator --------------------------
EXTENDS FiniteSets

CONSTANTS
    Clients,     \* set of clients
    Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
    unsat,       \* unsat[c] : resources requested by c but not yet allocated
    alloc        \* alloc[c] : resources currently held by c

vars == <<unsat, alloc>>

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

\* Resources not held by any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

(* A client with no outstanding requests that holds no resources
   may request a nonempty set of resources. *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(* The allocator gives a nonempty subset of the requested resources
   that are currently available (partial fulfillment allowed). *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq (available \cap unsat[c])
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* A client may return any nonempty subset of its held resources at any time. *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat

Next ==
    \E c \in Clients, S \in SUBSET Resources :
        \/ Request(c, S)
        \/ Allocate(c, S)
        \/ Return(c, S)

(* Fairness:
   - clients return their full allocation with weak fairness once fully satisfied
   - allocation of each requested resource is strongly fair *)
Liveness ==
    /\ \A c \in Clients :
          WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
    /\ \A c \in Clients, r \in Resources :
          SF_vars(Allocate(c, {r}))

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Safety: mutual exclusion *)
Mutex ==
    \A c1, c2 \in Clients :
        \A r \in Resources :
            r \in alloc[c1] \cap alloc[c2] => c1 = c2

(* Liveness: eventual return *)
ClientsWillReturn ==
    \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

(* Liveness: eventual allocation *)
ClientsWillObtain ==
    \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

(* Liveness: every client's request is satisfied infinitely often *)
InfOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Mutex)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
=============================================================================