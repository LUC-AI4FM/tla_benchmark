MODULE ResourceAllocator

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  CLIENTS,
  RESOURCES,
  INIT_ORDER   \* initial permutation of CLIENTS

VARIABLES alloc, reqs, order

(****************************************************************)
(* Helper definitions *)

Permutation(seq, set) ==
  /\ Len(seq) = Cardinality(set)
  /\ SET(seq) = set

UnionAlloc == \cup_{c ∈ CLIENTS} alloc[c]

FreeRes == RESOURCES \ UnionAlloc

ClientIdle(c) == alloc[c] = {} /\ reqs[c] = {}

(****************************************************************)
(* Initial state *)

Init ==
  /\ alloc = [c ∈ CLIENTS |-> {}]
  /\ reqs = [c ∈ CLIENTS |-> {}]
  /\ order = INIT_ORDER
  /\ Permutation(order, CLIENTS)

(****************************************************************)
(* Actions *)

RequestAction ==
  \E c ∈ CLIENTS, R ⊆ RESOURCES :
    /\ ClientIdle(c)
    /\ reqs' = [reqs EXCEPT ![c] = R]
    /\ UNCHANGED <<alloc, order>>

ServeAction ==
  \E c ∈ CLIENTS, S ⊆ {r ∈ reqs[c] : r ∈ FreeRes} :
    /\ order ≠ <<>>
    /\ FIRST(order) = c
    /\ S ≠ ∅
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] ∪ S]
    /\ reqs' = [reqs EXCEPT ![c] = reqs[c] \ S]
    /\ order' = Append(Rest(order), FIRST(order))

ReturnAction ==
  \E c ∈ CLIENTS, S ⊆ alloc[c] :
    /\ S ≠ ∅
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED <<reqs, order>>

RotateAction ==
  /\ order ≠ <<>>
  /\ order' = Append(Rest(order), FIRST(order))
  /\ UNCHANGED <<alloc, reqs>>

IdleAction ==
  /\ UNCHANGED <<alloc, reqs, order>>

Next ==
  \/ RequestAction
  \/ ServeAction
  \/ ReturnAction
  \/ RotateAction
  \/ IdleAction

(****************************************************************)
(* Type invariants *)

TypeInv ==
  /\ alloc \in [CLIENTS -> SUBSET RESOURCES]
  /\ reqs \in [CLIENTS -> SUBSET RESOURCES]
  /\ order ∈ Seq CLIENTS
  /\ Permutation(order, CLIENTS)

(****************************************************************)
(* Mutual exclusion invariant *)

MutualExcl ==
  \A r ∈ RESOURCES : Cardinality({c ∈ CLIENTS : r ∈ alloc[c]}) <= 1

(****************************************************************)
(* Liveness properties *)

EventualObtain ==
  \A c ∈ CLIENTS : [] (reqs[c] ≠ {} => <> (reqs[c] = {}))

EventuallyReturn ==
  \A c ∈ CLIENTS : [] ((alloc[c] ≠ {}) /\ reqs[c] = {}) => <> (alloc[c] = {})

(****************************************************************)
(* Fairness assumptions *)

Fairness ==
  WeakFair(ReturnAction) /\ WeakFair(ServeAction) /\ WeakFair(RotateAction)

(****************************************************************)
(* Specification *)

Spec ==
  Init
  /\ [][Next]_<<alloc, reqs, order>>
  /\ TypeInv
  /\ MutualExcl
  /\ EventualObtain
  /\ EventuallyReturn
  /\ Fairness

============================================================================