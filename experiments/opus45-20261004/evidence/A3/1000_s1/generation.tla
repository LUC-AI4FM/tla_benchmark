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
    Clients,        \* The set of clients
    Resources       \* The set of resources

VARIABLES
    unsat,          \* unsat[c] is the set of resources requested but not yet allocated to client c
    alloc           \* alloc[c] is the set of resources currently held by client c

vars == <<unsat, alloc>>

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(***************************************************************************)
(* The set of resources currently available (not held by any client)       *)
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
(* A client may only request when it holds no resources and has no         *)
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
(* Only resources that were requested (in unsat[c]) can be allocated.      *)
(***************************************************************************)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(***************************************************************************)
(* Client c returns all resources it currently holds.                      *)
(* A client may return resources even before its request is fully          *)
(* satisfied; this also cancels any remaining unsatisfied part.            *)
(***************************************************************************)
Return(c) ==
    /\ alloc[c] # {}
    /\ alloc' = [alloc EXCEPT ![c] = {}]
    /\ unsat' = [unsat EXCEPT ![c] = {}]

(***************************************************************************)
(* The next-state relation                                                 *)
(***************************************************************************)
Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ Return(c)

(***************************************************************************)
(* Safety: Mutual exclusion - no resource is held by more than one client  *)
(***************************************************************************)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(***************************************************************************)
(* Safety: A resource cannot be both allocated and available               *)
(***************************************************************************)
AllocatedNotAvailable ==
    \A c \in Clients : alloc[c] \cap available = {}

(***************************************************************************)
(* Combined safety invariant                                               *)
(***************************************************************************)
Safety == TypeOK /\ MutualExclusion

(***************************************************************************)
(* Weak fairness specification                                             *)
(***************************************************************************)
WeakFairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : WF_vars(Return(c))
    /\ \A c \in Clients : \A S \in SUBSET Resources : WF_vars(Allocate(c, S))

(***************************************************************************)
(* Strong fairness specification                                           *)
(***************************************************************************)
StrongFairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : SF_vars(Return(c))
    /\ \A c \in Clients : \A S \in SUBSET Resources : SF_vars(Allocate(c, S))

(***************************************************************************)
(* The basic specification without fairness                                *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Liveness: Every client eventually returns its resources                 *)
(***************************************************************************)
EventualReturn ==
    \A c \in Clients : alloc[c] # {} ~> alloc[c] = {}

(***************************************************************************)
(* Liveness: Every client request is eventually satisfied                  *)
(***************************************************************************)
EventualObtainment ==
    \A c \in Clients : unsat[c] # {} ~> unsat[c] = {}

(***************************************************************************)
(* Liveness: Infinitely often there are no unsatisfied requests            *)
(***************************************************************************)
InfinitelyOftenNoUnsatisfied ==
    []<>(\A c \in Clients : unsat[c] = {})

(***************************************************************************)
(* Liveness: Infinitely often all resources are available                  *)
(***************************************************************************)
InfinitelyOftenAllAvailable ==
    []<>(available = Resources)

(***************************************************************************)
(* Combined liveness property under strong fairness                        *)
(***************************************************************************)
Liveness ==
    /\ EventualReturn
    /\ EventualObtainment
    /\ InfinitelyOftenNoUnsatisfied

(***************************************************************************)
(* Symmetry expression for model checking                                  *)
(***************************************************************************)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

(***************************************************************************)
(* Concrete counterexample value structure for debugging                   *)
(* Example with 2 clients and 2 resources                                  *)
(***************************************************************************)
CounterexampleClients == {"c1", "c2"}
CounterexampleResources == {"r1", "r2"}

(***************************************************************************)
(* A specific state that could appear in a counterexample trace            *)
(***************************************************************************)
CounterexampleState ==
    /\ unsat = [c \in {"c1", "c2"} |-> IF c = "c1" THEN {"r1"} ELSE {}]
    /\ alloc = [c \in {"c1", "c2"} |-> IF c = "c2" THEN {"r1"} ELSE {}]

(***************************************************************************)
(* Theorems stating that the specifications satisfy the properties         *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => []Safety
THEOREM WeakFairSpec => EventualReturn
THEOREM StrongFairSpec => Liveness

================================================================================