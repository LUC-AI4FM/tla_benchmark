---------------------------- MODULE ResourceAllocator ----------------------------
(***************************************************************************)
(* This module specifies a simple resource allocator for a finite set of   *)
(* resources and a set of clients. Clients issue requests only when they   *)
(* currently hold no resources and have no outstanding unsatisfied request;*)
(* requests may then be partially fulfilled over time, and clients may     *)
(* return held resources even before a request is completely satisfied.    *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Clients,        \* The set of all clients
    Resources       \* The set of all resources

VARIABLES
    requested,      \* requested[c] = set of resources requested by client c
    allocated,      \* allocated[c] = set of resources currently held by client c
    available       \* The set of resources currently available (not allocated)

vars == <<requested, allocated, available>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ requested \in [Clients -> SUBSET Resources]
    /\ allocated \in [Clients -> SUBSET Resources]
    /\ available \subseteq Resources

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)
Init ==
    /\ requested = [c \in Clients |-> {}]
    /\ allocated = [c \in Clients |-> {}]
    /\ available = Resources

(***************************************************************************)
(* A client c requests a non-empty set S of resources.                     *)
(* Clients can only request when they hold no resources and have no        *)
(* outstanding unsatisfied request.                                        *)
(***************************************************************************)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ allocated[c] = {}
    /\ requested[c] = {}
    /\ requested' = [requested EXCEPT ![c] = S]
    /\ UNCHANGED <<allocated, available>>

(***************************************************************************)
(* Allocate a non-empty subset S of available resources to client c        *)
(* to partially or fully satisfy c's request.                              *)
(***************************************************************************)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq requested[c]
    /\ allocated' = [allocated EXCEPT ![c] = @ \union S]
    /\ requested' = [requested EXCEPT ![c] = @ \ S]
    /\ available' = available \ S

(***************************************************************************)
(* Client c returns all resources it currently holds.                      *)
(* A client may return resources even before its request is fully satisfied*)
(***************************************************************************)
Return(c) ==
    /\ allocated[c] # {}
    /\ allocated' = [allocated EXCEPT ![c] = {}]
    /\ available' = available \union allocated[c]
    /\ UNCHANGED requested

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E c \in Clients : \E S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : \E S \in SUBSET available : Allocate(c, S)
    \/ \E c \in Clients : Return(c)

(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)

\* Weak fairness specification
WeakFairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : WF_vars(Return(c))
    /\ \A c \in Clients : WF_vars(\E S \in SUBSET available : Allocate(c, S))

\* Strong fairness specification  
StrongFairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : WF_vars(Return(c))
    /\ \A c \in Clients : SF_vars(\E S \in SUBSET available : Allocate(c, S))

\* Default specification (weak fairness)
Spec == WeakFairSpec

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

(***************************************************************************)
(* Mutual exclusion: No resource is allocated to more than one client      *)
(***************************************************************************)
MutualExclusion ==
    \A c1, c2 \in Clients :
        c1 # c2 => allocated[c1] \cap allocated[c2] = {}

(***************************************************************************)
(* Resource conservation: All resources are accounted for                  *)
(***************************************************************************)
ResourceConservation ==
    available \union UNION {allocated[c] : c \in Clients} = Resources

(***************************************************************************)
(* No resource is both available and allocated                             *)
(***************************************************************************)
NoOverlap ==
    \A c \in Clients : available \cap allocated[c] = {}

(***************************************************************************)
(* Combined safety invariant                                               *)
(***************************************************************************)
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ResourceConservation
    /\ NoOverlap

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

(***************************************************************************)
(* Eventual return: If a client holds resources, it eventually returns them*)
(***************************************************************************)
EventualReturn ==
    \A c \in Clients : allocated[c] # {} ~> allocated[c] = {}

(***************************************************************************)
(* Eventual obtainment: If a client requests resources, it eventually      *)
(* obtains some resources (under strong fairness)                          *)
(***************************************************************************)
EventualObtainment ==
    \A c \in Clients : requested[c] # {} ~> allocated[c] # {}

(***************************************************************************)
(* Infinitely often no unsatisfied requests                                *)
(***************************************************************************)
InfinitelyOftenNoUnsatisfied ==
    []<>(\A c \in Clients : requested[c] = {})

(***************************************************************************)
(* Infinitely often all resources available                                *)
(***************************************************************************)
InfinitelyOftenAllAvailable ==
    []<>(available = Resources)

(***************************************************************************)
(* Symmetry for model checking                                             *)
(***************************************************************************)
Symmetry == Permutations(Clients) \union Permutations(Resources)

(***************************************************************************)
(* Concrete counterexample value structure for debugging                   *)
(***************************************************************************)
CounterexampleClients == {"c1", "c2"}
CounterexampleResources == {"r1", "r2"}

(***************************************************************************)
(* A state that demonstrates potential resource contention                 *)
(***************************************************************************)
CounterexampleState ==
    /\ requested = [c \in CounterexampleClients |-> 
                    IF c = "c1" THEN {"r1"} ELSE {"r1"}]
    /\ allocated = [c \in CounterexampleClients |-> {}]
    /\ available = {"r1", "r2"}

=============================================================================