--------------------------- MODULE SimpleAllocator ---------------------------
(***************************************************************************)
(* Specification of a simple resource allocator for a finite set of        *)
(* resources and a set of clients. A client may issue a request only when  *)
(* it holds no resources and has no outstanding unsatisfied request.       *)
(* Requests may be fulfilled partially over time, and a client may return  *)
(* held resources before its request is completely satisfied.              *)
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

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

(* Resources that are currently not allocated to any client. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* A client c that holds nothing and has no pending request may request S. *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator gives a nonempty subset of available requested resources. *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* A client returns some of the resources it holds. *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

(* Specification with weak fairness for allocation. *)
SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(* Specification with strong fairness for allocation. *)
SimpleAllocator2 ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
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

(* Symmetry for model checking. *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

(***************************************************************************)
(* A concrete counterexample structure showing that, under weak fairness,  *)
(* a client may be starved: two clients compete for the same resource.     *)
(***************************************************************************)
Counterexample ==
  LET c1 == CHOOSE c \in Clients : TRUE
      c2 == CHOOSE c \in Clients : c # c1
      r1 == CHOOSE r \in Resources : TRUE
      emp == [c \in Clients |-> {}]
  IN  [ states |->
          << [unsat |-> emp, alloc |-> emp],
             [unsat |-> [emp EXCEPT ![c1] = {r1}], alloc |-> emp],
             [unsat |-> [emp EXCEPT ![c1] = {r1}, ![c2] = {r1}], alloc |-> emp],
             [unsat |-> [emp EXCEPT ![c1] = {r1}], alloc |-> [emp EXCEPT ![c2] = {r1}]],
             [unsat |-> [emp EXCEPT ![c1] = {r1}], alloc |-> emp] >>,
        loop |-> 3 ]
=============================================================================