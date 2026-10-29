------------------------------ MODULE SimpleAllocator ------------------------------
(***************************************************************************)
(* A simple resource allocator for a finite set of resources and a set of  *)
(* clients.                                                                *)
(*                                                                         *)
(* - A client may issue a request only when it holds no resources and has  *)
(*   no outstanding unsatisfied request.                                   *)
(* - A request may be fulfilled partially, over several steps.             *)
(* - A client may return resources it holds before its request is fully    *)
(*   satisfied.                                                            *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c]: resources requested by c and not yet allocated
  alloc        \* alloc[c]: resources currently held by c

vars == <<unsat, alloc>>

-----------------------------------------------------------------------------------

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

(* Resources that no client currently holds. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* Client c requests the non-empty set S. It must hold nothing and have no *)
(* outstanding request.                                                    *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator gives client c the non-empty set S. S must be available   *)
(* and must be part of c's outstanding request. Partial fulfilment is      *)
(* allowed.                                                                *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns the non-empty set S of resources it holds. It may do   *)
(* this before its request is fully satisfied.                             *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-----------------------------------------------------------------------------------
(***************************************************************************)
(* Specification 1:                                                        *)
(*  - weak fairness for each client returning all the resources it holds; *)
(*  - weak fairness for allocating to each client.                         *)
(***************************************************************************)
SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

(***************************************************************************)
(* Specification 2:                                                        *)
(*  - clients return their resources only once their request is fully     *)
(*    satisfied (weak fairness);                                           *)
(*  - strong fairness for allocating to each client.                       *)
(***************************************************************************)
SimpleAllocator2 ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

-----------------------------------------------------------------------------------
(* Correctness properties *)

(* No resource is held by two different clients. *)
ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* A client whose request is fully satisfied eventually returns everything. *)
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

(* Every requested resource is eventually obtained. *)
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

(* Each client infinitely often has no unsatisfied request. *)
InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------------
(* Symmetry set for model checking with TLC *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-----------------------------------------------------------------------------------
THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator2 => ClientsWillObtain
THEOREM SimpleAllocator2 => InfOftenSatisfied

-----------------------------------------------------------------------------------
(***************************************************************************)
(* A concrete counterexample, written as a lasso-shaped behaviour, showing *)
(* that SimpleAllocator (weak fairness for Allocate) does not ensure       *)
(* ClientsWillObtain. The clients are "c1" and "c2"; the resources are     *)
(* "r1" and "r2". Both clients request both resources. Client c1 is        *)
(* repeatedly given r1 and returns it. Allocation to c2 is enabled only    *)
(* some of the time, and never continuously, so weak fairness never forces *)
(* it. The last state loops back to state number Loop.                     *)
(***************************************************************************)
CEState(u1, u2, a1, a2) ==
  [ unsat |-> ("c1" :> u1) @@ ("c2" :> u2),
    alloc |-> ("c1" :> a1) @@ ("c2" :> a2) ]

CounterExample ==
  [ states |->
      << CEState({},          {},          {},     {}),
         CEState({"r1","r2"}, {},          {},     {}),
         CEState({"r1","r2"}, {"r1","r2"}, {},     {}),
         CEState({"r1"},      {"r1","r2"}, {"r2"}, {}),
         CEState({},          {"r1","r2"}, {"r1","r2"}, {}),
         CEState({},          {"r1","r2"}, {"r2"},  {}),
         CEState({},          {"r1","r2"}, {},      {}),
         CEState({"r1","r2"}, {"r1","r2"}, {},      {}) >>,
    loop |-> 3 ]

=============================================================================================