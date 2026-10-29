------------------------ MODULE SimpleAllocator -------------------------
(***********************************************************************)
(* Specification of a simple allocator that manages a finite set of    *)
(* resources for a set of clients.                                     *)
(*                                                                     *)
(* - A client may issue a request only when it holds no resources and  *)
(*   has no outstanding unsatisfied request.                           *)
(* - A request may be fulfilled partially, over several steps.         *)
(* - A client may return resources it holds at any time, even before   *)
(*   its request has been completely satisfied.                        *)
(***********************************************************************)
EXTENDS FiniteSets, TLC

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c]: resources requested by c and not yet allocated
  alloc        \* alloc[c]: resources currently held by c

vars == <<unsat, alloc>>

-------------------------------------------------------------------------

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

(* Resources that no client currently holds *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

-------------------------------------------------------------------------

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* Client c requests the set S of resources. It may do so only when it  *)
(* holds nothing and has no outstanding request.                       *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator gives client c the resources in S, which must be a    *)
(* nonempty set of available resources that c is still waiting for.   *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns the nonempty set S of resources it currently holds.*)
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

-------------------------------------------------------------------------

(* First specification: weak fairness for returning all held          *)
(* resources and for allocation.                                       *)
SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(* Second specification: clients are only required to return their    *)
(* resources once their request has been completely satisfied, and    *)
(* allocation is assumed to be strongly fair.                          *)
SimpleAllocator2 ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

Spec == SimpleAllocator

-------------------------------------------------------------------------
(* Correctness properties *)

(* No resource is held by two different clients at the same time. *)
ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* A client whose request is fully satisfied eventually returns all    *)
(* its resources.                                                      *)
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

(* Every requested resource is eventually obtained by the client. *)
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

(* Infinitely often, every client has no unsatisfied request. *)
InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

(* Symmetry set for model checking with TLC. *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-------------------------------------------------------------------------
(* Theorems *)

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator2 => ClientsWillObtain
THEOREM SimpleAllocator2 => InfOftenSatisfied

THEOREM SimpleAllocator2 => []TypeInvariant
THEOREM SimpleAllocator2 => []ResourceMutex

-------------------------------------------------------------------------
(* A concrete counterexample, showing that under SimpleAllocator       *)
(* (weak fairness only) ClientsWillObtain can fail: two clients c1, c2 *)
(* compete for resources r1, r2, and the allocator keeps giving each   *)
(* client only part of what it needs while the other one holds the    *)
(* rest; partial returns let the cycle repeat forever.                 *)
(* The structure records the states of a lasso-shaped behavior and the *)
(* index of the state at which the loop starts.                        *)

CounterExample ==
  [ states |->
      << [ unsat |-> [c1 |-> {},             c2 |-> {}],
           alloc |-> [c1 |-> {},             c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"},   c2 |-> {}],
           alloc |-> [c1 |-> {},             c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"},   c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {},             c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r2"},         c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {"r1"},         c2 |-> {}] ],
         [ unsat |-> [c1 |-> {"r2"},         c2 |-> {"r1"}],
           alloc |-> [c1 |-> {"r1"},         c2 |-> {"r2"}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"},   c2 |-> {"r1"}],
           alloc |-> [c1 |-> {},             c2 |-> {"r2"}] ],
         [ unsat |-> [c1 |-> {"r1", "r2"},   c2 |-> {"r1", "r2"}],
           alloc |-> [c1 |-> {},             c2 |-> {}] ] >>,
    loop |-> 3,
    violated |-> "ClientsWillObtain" ]

=========================================================================