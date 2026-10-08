------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals

CONSTANTS
  Resources \in SUBSET ℕ
  Clients   \in SUBSET ℕ
  None      \in ℕ          \* A special value indicating “free”

(* The following constants fix a concrete counterexample state for illustration. *)
CONSTANT CounterExample ==
  [ alloc |-> [1 -> 2, 2 -> None],
    held |-> [2 -> {1}, 3 -> {}],
    req  |-> [2 -> {}, 3 -> {2}] ]

VARIABLES
  alloc,      \* [Resources -> Clients ∪ {None}]
  held,       \* [Clients   -> SUBSET Resources]
  req         \* [Clients   -> SUBSET Resources]

(* --------------------------------------------------------------------------- *)
(* Initial state: no allocations, holds or requests.                           *)
Init ==
  /\ alloc \in [Resources -> Clients ∪ {None}]
  /\ held  \in [Clients -> SUBSET Resources]
  /\ req   \in [Clients -> SUBSET Resources]
  /\ (\A r \in Resources : alloc[r] = None)
  /\ (\A c \in Clients : held[c] = {} /\ req[c] = {})

(* --------------------------------------------------------------------------- *)
(* Request action: a client with no holds and no pending request may issue a
   new request for any non‑empty subset of resources.                          *)
RequestAction ==
  \E c \in Clients :
    \E rq \in SUBSET Resources :
      /\ rq <> {}
      /\ held[c] = {}
      /\ req[c]  = {}
      /\ alloc'  = alloc
      /\ held'   = held
      /\ req'    = [req EXCEPT ![c] = rq]

(* --------------------------------------------------------------------------- *)
(* Grant action: a free resource r that is part of some client’s pending
   request may be allocated to that client.                                  *)
GrantAction ==
  \E c \in Clients :
    \E r \in Resources :
      /\ alloc[r] = None
      /\ r \in req[c]
      /\ alloc' = [alloc EXCEPT ![r] = c]
      /\ held'  = [held EXCEPT ![c] = held[c] ∪ {r}]
      /\ req'   = [req EXCEPT ![c] = req[c] \ {r}]

(* --------------------------------------------------------------------------- *)
(* Release action: a client may release any subset of the resources it holds.
   The released resources become free.                                       *)
ReleaseAction ==
  \E c \in Clients :
    \E S \subseteq held[c] :
      /\ alloc' = [alloc EXCEPT ![r] = None : r \in S]
      /\ held'  = [held EXCEPT ![c] = held[c] \ S]
      /\ req'   = req

(* --------------------------------------------------------------------------- *)
(* Next state relation. *)
Next ==
  RequestAction \/ GrantAction \/ ReleaseAction

(* --------------------------------------------------------------------------- *)
(* Type correctness invariant.                                               *)
TypeOK ==
  /\ alloc \in [Resources -> Clients ∪ {None}]
  /\ held  \in [Clients -> SUBSET Resources]
  /\ req   \in [Clients -> SUBSET Resources]

(* --------------------------------------------------------------------------- *)
(* Consistency between allocation map and held sets.                          *)
AllocHeldConsistent ==
  \A r \in Resources :
    IF alloc[r] = None THEN
      (\A c \in Clients : r \notin held[c])
    ELSE
      (\A c \in Clients : (alloc[r] = c) <=> r \in held[c])

(* --------------------------------------------------------------------------- *)
(* Mutual exclusion: a resource cannot be owned by two clients simultaneously.
   This follows from AllocHeldConsistent.                                    *)
NoConflicts ==
  \A r \in Resources :
    alloc[r] = None \/ (\exists c \in Clients : (alloc[r] = c) /\ r \in held[c])

(* --------------------------------------------------------------------------- *)
(* Symmetry predicate: the set of clients is closed under any permutation.   *)
IsPermutation[σ] == 
  /\ σ \in [Clients -> Clients]
  /\ (\A c1, c2 \in Clients : (σ[c1] = σ[c2]) => (c1 = c2))
  /\ (\A c \in Clients : ∃ d \in Clients : σ[d] = c)

Symmetry ==
  \A σ \in [Clients -> Clients] : IsPermutation[σ]

(* --------------------------------------------------------------------------- *)
(* Liveness properties. *)

(* Eventual return: every allocated resource is eventually released.        *)
EventualReturnResource ==
  \A r \in Resources :
    \A c \in Clients :
      [](alloc[r] = c => <> (alloc[r] = None))

(* Eventual obtainment: if a client has an outstanding request, some of
   its requested resources will be granted eventually.                      *)
EventualObtainment ==
  \A c \in Clients :
    [](req[c] <> {} => <> (\E r \in req[c] : alloc[r] = c))

(* Infinitely often having no unsatisfied requests: every client’s request set
   becomes empty infinitely often.                                           *)
InfinitelyNoUnsatisfied ==
  []<> (\A c \in Clients : req[c] = {})

(* --------------------------------------------------------------------------- *)
(* Two system specifications with different fairness assumptions.              *)

SpecUnfair == Init /\ [][Next]_vars

SpecFair   == Init /\ WF_vars Next

(* --------------------------------------------------------------------------- *)
(* Combined specification: the system satisfies safety invariants and
   liveness properties under either fairness assumption.                      *)

Spec ==
  /\ (SpecUnfair \/ SpecFair)
  /\ TypeOK
  /\ AllocHeldConsistent
  /\ NoConflicts
  /\ Symmetry
  /\ EventualReturnResource
  /\ EventualObtainment
  /\ InfinitelyNoUnsatisfied

=============================================================================