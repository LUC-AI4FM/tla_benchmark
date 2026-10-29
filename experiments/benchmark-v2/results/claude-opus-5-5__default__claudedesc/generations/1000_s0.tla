--------------------------- MODULE SimpleAllocator ---------------------------
(***************************************************************************)
(* A simple resource allocator that manages a finite set of shared         *)
(* resources among a set of clients.                                       *)
(*                                                                         *)
(* Model configuration:                                                    *)
(*   Clients   <- {c1, c2, c3}   (three clients, model values)             *)
(*   Resources <- {r1, r2}       (two resources, model values)             *)
(*   SPECIFICATION SimpleAllocator                                         *)
(*   INVARIANTS TypeInvariant ResourceMutex                                *)
(*   PROPERTIES ClientsWillReturn ClientsWillObtain InfOftenSatisfied      *)
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

-----------------------------------------------------------------------------
(* Resources that are not currently allocated to any client. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* Client c requests the nonempty set S, only when it holds nothing and   *)
(* has no pending request.                                                 *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* The allocator grants a nonempty subset S of available resources that   *)
(* the client has requested (possibly only partially satisfying it).      *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a nonempty subset S of the resources it holds, even   *)
(* before its whole request is satisfied.                                 *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

-----------------------------------------------------------------------------
(* Principal specification. *)
SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

Spec == SimpleAllocator

-----------------------------------------------------------------------------
(* Correctness properties. *)

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
(* Weaker variant: clients are only required to return their resources    *)
(* after their entire request has been satisfied.                         *)
SimpleAllocator2 ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

-----------------------------------------------------------------------------
THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied

THEOREM SimpleAllocator2 => []TypeInvariant
THEOREM SimpleAllocator2 => []ResourceMutex
THEOREM SimpleAllocator2 => ClientsWillReturn
(* Note: SimpleAllocator2 does NOT imply ClientsWillObtain or             *)
(* InfOftenSatisfied: clients may each hold part of the resources and     *)
(* wait for the rest forever (deadlock-like starvation).                  *)
=============================================================================