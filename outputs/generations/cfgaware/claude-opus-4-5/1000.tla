---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Clients, Resources

VARIABLES unsat,    \* unsat[c] = set of resources requested but not yet allocated to client c
          alloc     \* alloc[c] = set of resources currently held by client c

vars == <<unsat, alloc>>

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK == 
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(* Available resources: those not allocated to any client *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

-----------------------------------------------------------------------------
(* Initial state: no requests, no allocations *)
Init == 
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

-----------------------------------------------------------------------------
(* Client c requests a non-empty set S of resources.
   Precondition: c currently holds no resources and has no outstanding request. *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(* Allocate a non-empty subset S of c's unsatisfied request from available resources *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq unsat[c]
    /\ S \subseteq available
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

(* Client c returns a non-empty subset S of its held resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
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

(* Weak fairness on all actions *)
WeakFairness == 
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           WF_vars(Request(c, S))
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           WF_vars(Allocate(c, S))
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           WF_vars(Return(c, S))

(* Strong fairness on allocation, weak fairness on others *)
StrongFairness ==
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           WF_vars(Request(c, S))
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           SF_vars(Allocate(c, S))
    /\ \A c \in Clients : \A S \in SUBSET Resources : 
           WF_vars(Return(c, S))

-----------------------------------------------------------------------------
(* System specifications *)

Spec == Init /\ [][Next]_vars /\ WeakFairness

FairSpec == Init /\ [][Next]_vars /\ StrongFairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* Mutual exclusion: no resource is allocated to two different clients *)
MutualExclusion == 
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* A resource is either available or allocated to exactly one client *)
ResourceInvariant ==
    \A r \in Resources :
        Cardinality({c \in Clients : r \in alloc[c]}) <= 1

Safety == TypeOK /\ MutualExclusion

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every client that requests resources eventually gets them all *)
EventualObtainment == 
    \A c \in Clients : (unsat[c] # {}) ~> (unsat[c] = {})

(* Every client that holds resources eventually returns them all *)
EventualReturn == 
    \A c \in Clients : (alloc[c] # {}) ~> (alloc[c] = {})

(* Infinitely often, there are no unsatisfied requests *)
InfinitelyOftenNoUnsat == 
    []<>(\A c \in Clients : unsat[c] = {})

Liveness == EventualObtainment /\ EventualReturn /\ InfinitelyOftenNoUnsat

-----------------------------------------------------------------------------
(* Symmetry for model checking *)
Symmetry == Permutations(Clients) \union Permutations(Resources)

-----------------------------------------------------------------------------
(* Concrete counterexample structure for debugging/testing *)
CounterExample == 
    [client |-> CHOOSE c \in Clients : TRUE,
     resources |-> Resources,
     state |-> [unsat |-> unsat, alloc |-> alloc]]

-----------------------------------------------------------------------------
(* Theorems to be verified *)

THEOREM Spec => []TypeOK

THEOREM Spec => []MutualExclusion

THEOREM FairSpec => EventualObtainment

THEOREM FairSpec => EventualReturn

THEOREM FairSpec => InfinitelyOftenNoUnsat

=============================================================================