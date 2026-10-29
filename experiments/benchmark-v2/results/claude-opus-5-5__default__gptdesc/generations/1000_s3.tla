---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS FiniteSets, TLC

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c]: set of resources requested by c but not yet obtained
  alloc        \* alloc[c]: set of resources currently held by client c

vars == <<unsat, alloc>>

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

available == Resources \ (UNION {alloc[c] : c \in Clients})

-----------------------------------------------------------------------------
Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* A client may request a set of resources only if it holds no resources   *)
(* and has no outstanding unsatisfied request.                             *)
Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator may partially fulfil a request using available resources. *)
Allocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* A client may return held resources, even before its request is fully    *)
(* satisfied.                                                              *)
Return(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-----------------------------------------------------------------------------
(* First specification: weak fairness for returning and allocation.        *)
SimpleAllocator ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(* Second specification: clients return only once fully satisfied (weak   *)
(* fairness), and allocation is strongly fair.                             *)
SimpleAllocator2 ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

Spec == SimpleAllocator2

-----------------------------------------------------------------------------
(* Properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : unsat[c] = {} ~> alloc[c] = {}

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator2 => ClientsWillObtain
THEOREM SimpleAllocator2 => InfOftenSatisfied

-----------------------------------------------------------------------------
(* Symmetry for model checking *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-----------------------------------------------------------------------------
(* A concrete counterexample (to ClientsWillObtain under SimpleAllocator) *)
(* with two clients c1, c2 and two resources r1, r2: each client grabs one *)
(* resource of its request, returns it, and the cycle repeats forever so  *)
(* that neither request is ever completely satisfied.                      *)
CounterExample ==
  << [unsat |-> [c1 |-> {}, c2 |-> {}],
      alloc |-> [c1 |-> {}, c2 |-> {}]],
     [unsat |-> [c1 |-> {"r1","r2"}, c2 |-> {}],
      alloc |-> [c1 |-> {}, c2 |-> {}]],
     [unsat |-> [c1 |-> {"r1","r2"}, c2 |-> {"r1","r2"}],
      alloc |-> [c1 |-> {}, c2 |-> {}]],
     [unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1","r2"}],
      alloc |-> [c1 |-> {"r1"}, c2 |-> {}]],
     [unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1"}],
      alloc |-> [c1 |-> {"r1"}, c2 |-> {"r2"}]],
     [unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1"}],
      alloc |-> [c1 |-> {}, c2 |-> {"r2"}]],
     [unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1"}],
      alloc |-> [c1 |-> {}, c2 |-> {}]] >>

=============================================================================