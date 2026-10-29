------------------------- MODULE SimpleAllocator -------------------------
(*************************************************************************)
(* Specification of an allocator managing a finite set of resources     *)
(* shared among a set of clients.  A client may issue a request only    *)
(* when it holds no resources and has no outstanding unsatisfied        *)
(* request.  Requests may be satisfied in several steps, and a client   *)
(* may return resources before its request is completely satisfied.     *)
(*************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c] : resources requested by c but not yet allocated
  alloc        \* alloc[c] : resources currently allocated to c

vars == <<unsat, alloc>>

-------------------------------------------------------------------------

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

(* Resources not currently allocated to any client *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* Client c requests the set S of resources. *)
Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator grants a (partial) allocation S to client c. *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns the set S of resources it holds. *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-------------------------------------------------------------------------

(* Safety-only specification *)
SimpleAllocator == Init /\ [][Next]_vars

(* Weak fairness for returning and for allocation *)
SimpleAllocator2 ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(* Weak fairness for returning, strong fairness for allocation *)
SimpleAllocator3 ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

-------------------------------------------------------------------------
(* Correctness properties *)

ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------
(* Symmetry for model checking *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-------------------------------------------------------------------------
(* Concrete counterexample to ClientsWillObtain under SimpleAllocator2:  *)
(* two clients c1, c2 and two resources r1, r2.  c2 repeatedly obtains   *)
(* and returns r1 while c1 waits for both resources; allocation to c1 is *)
(* enabled only intermittently, so weak fairness does not force it.      *)
Counterexample ==
  [ resources |-> {"r1", "r2"},
    clients   |-> {"c1", "c2"},
    trace     |->
      << [unsat |-> [c1 |-> {}, c2 |-> {}],
          alloc |-> [c1 |-> {}, c2 |-> {}]],
         [unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {}],
          alloc |-> [c1 |-> {}, c2 |-> {}]],
         [unsat |-> [c1 |-> {"r1", "r2"}, c2 |-> {"r1"}],
          alloc |-> [c1 |-> {}, c2 |-> {}]],
         [unsat |-> [c1 |-> {"r1"}, c2 |-> {"r1"}],
          alloc |-> [c1 |-> {"r2"}, c2 |-> {}]],
         [unsat |-> [c1 |-> {"r1"}, c2 |-> {}],
          alloc |-> [c1 |-> {"r2"}, c2 |-> {"r1"}]],
         [unsat |-> [c1 |-> {"r1"}, c2 |-> {}],
          alloc |-> [c1 |-> {"r2"}, c2 |-> {}]],
         [unsat |-> [c1 |-> {"r1"}, c2 |-> {"r1"}],
          alloc |-> [c1 |-> {"r2"}, c2 |-> {}]] >>,
    loopBack  |-> 4 ]

-------------------------------------------------------------------------
THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator2 => ClientsWillReturn
THEOREM SimpleAllocator3 => ClientsWillObtain
THEOREM SimpleAllocator3 => InfOftenSatisfied
=========================================================================