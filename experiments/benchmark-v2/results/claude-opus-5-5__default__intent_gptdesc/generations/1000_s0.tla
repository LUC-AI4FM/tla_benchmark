---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS FiniteSets, TLC

CONSTANTS
    Clients,      \* set of clients
    Resources     \* finite set of indistinguishable resources

ASSUME IsFiniteSet(Resources)

VARIABLES
    unsat,        \* unsat[c]: resources requested by c but not yet granted
    alloc         \* alloc[c]: resources currently held by c

vars == <<unsat, alloc>>

-------------------------------------------------------------------------------
TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

available == Resources \ (UNION {alloc[c] : c \in Clients})

-------------------------------------------------------------------------------
Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

(* Client c issues a new nonempty request S; allowed only when it holds
   nothing and has no outstanding request. *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(* The allocator grants c a nonempty set S of free resources that c requested. *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq (available \cap unsat[c])
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a nonempty subset S of the resources it holds. *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat

Next ==
    \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-------------------------------------------------------------------------------
(* Fairness:
   - Clients whose request has been fully satisfied must eventually return
     all resources they hold (weak fairness).
   - The allocator must eventually grant requested resources, even if they
     are only intermittently available (strong fairness). *)
Liveness ==
    /\ \A c \in Clients :
          WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
    /\ \A c \in Clients :
          SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
(* Safety properties *)

Mutex ==
    \A c1, c2 \in Clients :
        c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Well-formed state: outstanding requests and holdings are disjoint. *)
WellFormed ==
    \A c \in Clients : unsat[c] \cap alloc[c] = {}

Safety == TypeInvariant /\ Mutex /\ WellFormed

(* Liveness properties *)

(* Every requested resource is eventually granted. *)
ClientsWillObtain ==
    \A c \in Clients, r \in Resources :
        (r \in unsat[c]) ~> (r \in alloc[c])

(* Once a request is fully granted, the client eventually returns everything. *)
ClientsWillReturn ==
    \A c \in Clients :
        (unsat[c] = {}) ~> (alloc[c] = {})

(* Every client's outstanding request is satisfied infinitely often. *)
InfOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Mutex /\ WellFormed)
THEOREM Spec => ClientsWillObtain /\ ClientsWillReturn /\ InfOftenSatisfied

=============================================================================