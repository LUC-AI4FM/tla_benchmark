--------------------------- MODULE ResourceAllocator ---------------------------
(***************************************************************************)
(* This module specifies a simple resource allocator for a finite set of   *)
(* resources and a set of clients. Clients issue requests only when they   *)
(* currently hold no resources and have no outstanding unsatisfied         *)
(* request; requests may then be partially fulfilled over time, and        *)
(* clients may return held resources even before a request is completely   *)
(* satisfied.                                                              *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Resources,      \* The set of all resources
    Clients         \* The set of all clients

VARIABLES
    unsat,          \* unsat[c] is the set of resources client c has requested but not yet received
    alloc           \* alloc[c] is the set of resources currently allocated to client c

vars == <<unsat, alloc>>

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(***************************************************************************)
(* The set of resources currently available (not allocated to any client)  *)
(***************************************************************************)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(***************************************************************************)
(* Initial state: no requests and no allocations                           *)
(***************************************************************************)
Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

(***************************************************************************)
(* Client c requests a non-empty set S of resources.                       *)
(* A client can only request when it holds no resources and has no         *)
(* outstanding unsatisfied request.                                        *)
(***************************************************************************)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(***************************************************************************)
(* Allocate a non-empty set S of available resources to client c.          *)
(* S must be a subset of client c's unsatisfied requests.                  *)
(***************************************************************************)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(***************************************************************************)
(* Client c returns a non-empty set S of resources it currently holds.     *)
(* Clients may return resources even before their request is completely    *)
(* satisfied.                                                              *)
(***************************************************************************)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat

(***************************************************************************)
(* The next-state relation                                                 *)
(***************************************************************************)
Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ \E S \in SUBSET Resources : Return(c, S)

(***************************************************************************)
(* Safety: Mutual exclusion of resource ownership                          *)
(* No resource is allocated to more than one client at a time              *)
(***************************************************************************)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(***************************************************************************)
(* Safety: Resources are either available or allocated (resource           *)
(* conservation)                                                           *)
(***************************************************************************)
ResourceConservation ==
    \A r \in Resources :
        Cardinality({c \in Clients : r \in alloc[c]}) <= 1

(***************************************************************************)
(* Safety: Unsatisfied requests only contain resources not yet allocated   *)
(* to the requesting client                                                *)
(***************************************************************************)
UnsatNotAllocated ==
    \A c \in Clients : unsat[c] \cap alloc[c] = {}

(***************************************************************************)
(* Combined safety invariant                                               *)
(***************************************************************************)
SafetyInvariant ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ UnsatNotAllocated

(***************************************************************************)
(* Liveness: If a client holds resources, it eventually returns them       *)
(***************************************************************************)
EventualReturn ==
    \A c \in Clients : alloc[c] # {} ~> alloc[c] = {}

(***************************************************************************)
(* Liveness: If a client has an unsatisfied request, it is eventually      *)
(* satisfied (all requested resources are allocated)                       *)
(***************************************************************************)
EventualObtainment ==
    \A c \in Clients : unsat[c] # {} ~> unsat[c] = {}

(***************************************************************************)
(* Liveness: Infinitely often there are no unsatisfied requests            *)
(***************************************************************************)
InfinitelyOftenNoUnsatRequests ==
    []<>(\A c \in Clients : unsat[c] = {})

(***************************************************************************)
(* Specification with weak fairness on all actions                         *)
(***************************************************************************)
Fairness ==
    /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
    /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Return(c, S))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Specification with strong fairness (stronger liveness guarantees)       *)
(***************************************************************************)
StrongFairness ==
    /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))
    /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Return(c, S))

StrongSpec == Init /\ [][Next]_vars /\ StrongFairness

(***************************************************************************)
(* Liveness properties that hold under the specifications                  *)
(***************************************************************************)
LivenessSpec ==
    /\ EventualReturn
    /\ EventualObtainment
    /\ InfinitelyOftenNoUnsatRequests

(***************************************************************************)
(* Symmetry expression for model checking                                  *)
(* Both Clients and Resources can be permuted                              *)
(***************************************************************************)
Symmetry == Permutations(Clients) \union Permutations(Resources)

(***************************************************************************)
(* Concrete counterexample value structure for model checking              *)
(* This can be used to find specific counterexamples                       *)
(***************************************************************************)
CounterexampleClients == {"c1", "c2"}
CounterexampleResources == {"r1", "r2"}

(***************************************************************************)
(* A specific state that could be part of a counterexample                 *)
(***************************************************************************)
CounterexampleState ==
    /\ unsat = [c \in {"c1", "c2"} |-> IF c = "c1" THEN {"r1"} ELSE {"r2"}]
    /\ alloc = [c \in {"c1", "c2"} |-> {}]

=============================================================================