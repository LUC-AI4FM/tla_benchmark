---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Clients,      \* The set of clients
    Resources     \* The set of resources

VARIABLES
    unsat,        \* unsat[c] is the set of resources requested but not yet allocated to client c
    alloc         \* alloc[c] is the set of resources currently allocated to client c

vars == <<unsat, alloc>>

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK == 
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

(* A resource can be allocated to at most one client *)
MutualExclusion == 
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Available resources: those not allocated to any client *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

-----------------------------------------------------------------------------
(* Initial state: no requests, no allocations *)
Init == 
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

(* Client c requests a non-empty set S of resources *)
(* Precondition: c has no outstanding request and holds no resources *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

(* Allocate a non-empty subset S of available resources to client c *)
(* Precondition: S is a non-empty subset of c's unsatisfied request and all resources in S are available *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq unsat[c]
    /\ S \subseteq available
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a non-empty subset S of its allocated resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat

-----------------------------------------------------------------------------
(* Next state relation *)
Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ \E S \in SUBSET Resources : Return(c, S)

(* Specification without fairness *)
Spec == Init /\ [][Next]_vars

(* Specification with weak fairness on all actions *)
FairSpec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A c \in Clients : 
        /\ WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
        /\ WF_vars(\E S \in SUBSET Resources : Return(c, S))

-----------------------------------------------------------------------------
(* Safety properties *)

Safety == TypeOK /\ MutualExclusion

(* Liveness: Every request is eventually satisfied (client gets all requested resources) *)
EventualObtainment == 
    \A c \in Clients : unsat[c] # {} ~> unsat[c] = {}

(* Liveness: Every allocated resource is eventually returned *)
EventualReturn == 
    \A c \in Clients : alloc[c] # {} ~> alloc[c] = {}

(* Liveness: Infinitely often there are no unsatisfied requests *)
InfinitelyOftenNoUnsat == 
    []<>(\A c \in Clients : unsat[c] = {})

-----------------------------------------------------------------------------
(* Symmetry for model checking *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-----------------------------------------------------------------------------
(* Concrete counterexample value structure for debugging/testing *)
CounterexampleClients == {"c1", "c2"}
CounterexampleResources == {"r1", "r2"}

CounterexampleState == 
    /\ unsat = [c \in CounterexampleClients |-> IF c = "c1" THEN {"r1"} ELSE {}]
    /\ alloc = [c \in CounterexampleClients |-> IF c = "c2" THEN {"r1"} ELSE {}]

=============================================================================