---------------------------- MODULE ResourceAllocator ----------------------------
(***************************************************************************)
(* This module specifies a simple resource allocator for a finite set of   *)
(* resources and a set of clients. Clients issue requests only when they   *)
(* currently hold no resources and have no outstanding unsatisfied         *)
(* request; requests may then be partially fulfilled over time, and        *)
(* clients may return held resources even before a request is completely   *)
(* satisfied.                                                              *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Clients,     \* The set of clients
    Resources    \* The set of resources

VARIABLES
    unsat,       \* unsat[c] is the set of resources requested but not yet allocated to client c
    alloc        \* alloc[c] is the set of resources currently allocated to client c

vars == <<unsat, alloc>>

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(***************************************************************************)
(* The set of resources currently available (not allocated to any client)  *)
(***************************************************************************)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)
Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

(***************************************************************************)
(* A client c requests a non-empty set S of resources. A client may only   *)
(* request resources when it holds no resources and has no outstanding     *)
(* unsatisfied request.                                                    *)
(***************************************************************************)
Request(c, S) ==
    /\ alloc[c] = {}
    /\ unsat[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(***************************************************************************)
(* Allocate a non-empty subset S of available resources to client c,       *)
(* where S is a subset of c's unsatisfied requests.                        *)
(***************************************************************************)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(***************************************************************************)
(* Client c returns all resources it currently holds.                      *)
(***************************************************************************)
Return(c) ==
    /\ alloc[c] # {}
    /\ alloc' = [alloc EXCEPT ![c] = {}]
    /\ UNCHANGED unsat

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ Return(c)

(***************************************************************************)
(* Safety: Mutual exclusion of resource ownership                          *)
(* No resource is allocated to more than one client at a time.             *)
(***************************************************************************)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(***************************************************************************)
(* Safety: Allocated resources are consistent                              *)
(* A resource cannot be both allocated and in an unsatisfied request       *)
(* for different clients.                                                  *)
(***************************************************************************)
ResourceConsistency ==
    \A c \in Clients : alloc[c] \cap unsat[c] = {}

(***************************************************************************)
(* Safety invariant combining all safety properties                        *)
(***************************************************************************)
Safety == TypeOK /\ MutualExclusion /\ ResourceConsistency

(***************************************************************************)
(* Liveness: Every client that holds resources eventually returns them     *)
(***************************************************************************)
EventualReturn ==
    \A c \in Clients : alloc[c] # {} ~> alloc[c] = {}

(***************************************************************************)
(* Liveness: Every unsatisfied request is eventually satisfied             *)
(* (the client eventually obtains all requested resources)                 *)
(***************************************************************************)
EventualObtainment ==
    \A c \in Clients : unsat[c] # {} ~> unsat[c] = {}

(***************************************************************************)
(* Liveness: Infinitely often there are no unsatisfied requests            *)
(***************************************************************************)
InfinitelyOftenNoUnsat ==
    []<>(\A c \in Clients : unsat[c] = {})

(***************************************************************************)
(* Liveness: Infinitely often all resources are available                  *)
(***************************************************************************)
InfinitelyOftenAllAvailable ==
    []<>(available = Resources)

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
(* Basic specification (no fairness)                                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Symmetry for model checking                                             *)
(***************************************************************************)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

(***************************************************************************)
(* Concrete counterexample values for debugging/testing                    *)
(***************************************************************************)
CounterexampleClients == {"c1", "c2"}
CounterexampleResources == {"r1", "r2"}

(***************************************************************************)
(* A concrete state that violates mutual exclusion (for testing)           *)
(***************************************************************************)
CounterexampleState ==
    /\ unsat = [c \in CounterexampleClients |-> {}]
    /\ alloc = [c \in CounterexampleClients |-> 
                  IF c = "c1" THEN {"r1"} ELSE {"r1"}]  \* Both hold r1 - violation!

(***************************************************************************)
(* Theorems (properties that should hold)                                  *)
(***************************************************************************)

THEOREM Spec => []TypeOK

THEOREM Spec => []MutualExclusion

THEOREM Spec => []ResourceConsistency

THEOREM Spec => []Safety

THEOREM WeakFairSpec => EventualReturn

THEOREM StrongFairSpec => EventualObtainment

THEOREM StrongFairSpec => InfinitelyOftenNoUnsat

=============================================================================