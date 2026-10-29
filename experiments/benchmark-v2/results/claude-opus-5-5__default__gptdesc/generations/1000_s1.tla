------------------------- MODULE SimpleAllocator -------------------------
(***************************************************************************)
(* Specification of a simple allocator managing a finite set of resources  *)
(* that are requested and returned by a set of clients.                    *)
(*                                                                         *)
(* - A client may issue a request only when it holds no resources and has  *)
(*   no outstanding unsatisfied request.                                   *)
(* - A request may be fulfilled partially, over several allocation steps.  *)
(* - A client may return resources it holds at any time, even before its   *)
(*   request has been completely satisfied.                                *)
(***************************************************************************)
EXTENDS FiniteSets, TLC

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c] denotes the outstanding requests of client c
  alloc        \* alloc[c] denotes the resources allocated to client c

vars == <<unsat, alloc>>

-------------------------------------------------------------------------

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

(* Resources that are currently not held by any client. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

-------------------------------------------------------------------------

(* Initially, no resources have been requested or allocated. *)
Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* A client c may request a set S of resources provided that all of its    *)
(* previous requests have been satisfied and that it holds no resources.   *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* Allocation of a set S of available resources to a client that has       *)
(* requested them (the entire request does not have to be filled).         *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a set S of resources that it holds. It may do so even  *)
(* before its full request has been honored.                               *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

(* The next-state relation. *)
Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-------------------------------------------------------------------------

(* First specification: clients eventually return all resources they hold, *)
(* and allocation to every client is weakly fair.                          *)
SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(* Second specification: clients only need to return resources once their  *)
(* request has been completely satisfied, and allocation is strongly fair. *)
SimpleAllocator2 ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

Spec == SimpleAllocator

Spec2 == SimpleAllocator2

-------------------------------------------------------------------------
(* Correctness properties. *)

(* Mutual exclusion: no resource is allocated to two different clients. *)
ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

Safety == ResourceMutex

(* Every client whose request has been satisfied will eventually return   *)
(* all of its resources.                                                  *)
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {} ~> alloc[c] = {})

(* Every client will eventually obtain every resource it has requested.  *)
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

(* Infinitely often, there are no unsatisfied requests at all. *)
InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

Liveness == ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied

-------------------------------------------------------------------------
(* Symmetry for model checking with TLC. *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-------------------------------------------------------------------------
(* A concrete counterexample (lasso-shaped trace) showing that             *)
(* SimpleAllocator does not guarantee ClientsWillObtain: two clients both  *)
(* request two resources and keep receiving one each and returning it,     *)
(* so neither request is ever completely satisfied.                        *)
CounterExample ==
  [ states |->
      << [ unsat |-> [c1 |-> {}, c2 |-> {}],
           alloc |-> [c1 |-> {}, c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {}],
           alloc |-> [c1 |-> {}, c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {}, c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {"r1"}, c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r2"}, c2 |-> {"r1"}],
           alloc |-> [c1 |-> {"r1"}, c2 |-> {"r2"}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {"r1"}],
           alloc |-> [c1 |-> {}, c2 |-> {"r2"}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {}, c2 |-> {}] ] >>,
    loop |-> 3 ]

-------------------------------------------------------------------------
(* Theorems. *)

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator2 => []TypeInvariant
THEOREM SimpleAllocator2 => []ResourceMutex
THEOREM SimpleAllocator2 => ClientsWillObtain
THEOREM SimpleAllocator2 => InfOftenSatisfied

=========================================================================