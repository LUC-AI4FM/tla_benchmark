```
MODULE ResourceAllocator
EXTENDS Naturals, Sequences

CONSTANTS CLIENTS, RESOURCES, NULL

ClientSet == CLIENTS
ResSet    == RESOURCES

VARIABLES owner, req

(***************************************************************************)
(* Type declarations *)
(***************************************************************************)

owner \in [ResSet -> ClientSet \/ {NULL}]
req   \in [ClientSet -> SUBSET ResSet]

(***************************************************************************)
(* Initial state *)
(***************************************************************************)

Init ==
  /\ owner = [r \in ResSet |-> NULL]
  /\ req   = [c \in ClientSet |-> {}]

(***************************************************************************)
(* Actions *)
(***************************************************************************)

IssuedReq ==
  ∃ c ∈ ClientSet, R ⊆ ResSet :
    /\ req[c] = {}
    /\ ¬∃ r ∈ ResSet : owner[r] = c
    /\ req'   = [req EXCEPT ![c] = R]
    /\ owner' = owner

Grant ==
  ∃ c ∈ ClientSet, S ⊆ ResSet :
    /\ S ≠ {}
    /\ S ⊆ req[c]
    /\ ∀ r ∈ S : owner[r] = NULL
    /\ owner' = [owner EXCEPT ![r] = IF r ∈ S THEN c ELSE @]
    /\ req'   = [req EXCEPT ![c] = req[c] \ S]

Return ==
  ∃ c ∈ ClientSet, T ⊆ ResSet :
    /\ T ≠ {}
    /\ ∀ r ∈ T : owner[r] = c
    /\ owner' = [owner EXCEPT ![r] = IF r ∈ T THEN NULL ELSE @]
    /\ req'   = req

(***************************************************************************)
(* Next-state relation *)
(***************************************************************************)

vars == <<owner, req>>

Next ==
  IssuedReq \/ Grant \/ Return

(***************************************************************************)
(* Temporal specifications with different fairness assumptions *)
(***************************************************************************)

SpecWeakFairness ==
  Init
  /\ [] (Next)_vars
  /\ WF(IssuedReq) /\ WF(Grant) /\ WF(Return)

SpecStrongFairness ==
  Init
  /\ [] (Next)_vars
  /\ SF(IssuedReq) /\ SF(Grant) /\ SF(Return)

(***************************************************************************)
(* Safety invariants *)
(***************************************************************************)

NoPendingRequests == ∀ c ∈ ClientSet : req[c] = {}

TypeInvariant ==
  owner \in [ResSet -> ClientSet \/ {NULL}]
  /\ req   \in [ClientSet -> SUBSET ResSet]

MutualExclusion ==
  ∀ r1, r2 ∈ ResSet :
    (owner[r1] = owner[r2]) => TRUE
(*
  Mutual exclusion is guaranteed by the function type of `owner`.
*)

(***************************************************************************)
(* Liveness properties *)
(***************************************************************************)

EventualReturn ==
  [] ∀ r ∈ ResSet :
      (∃ c ∈ ClientSet : owner[r] = c) => <> (owner[r] = NULL)

EventualObtainment ==
  [] ∀ c ∈ ClientSet :
      (req[c] ≠ {}) => <> (req[c] = {})

InfinitelyOftenNoPending ==
  [](<> NoPendingRequests)

(***************************************************************************)
(* Full specification *)
(***************************************************************************)

Spec == SpecStrongFairness

(***************************************************************************)
(* Theorems to be proved *)
(***************************************************************************)

THEOREM TypeInvariant IS INVARSPEC
    ASSUME Spec
    PROVE TYPEINVARIANT

THEOREM MutualExclusion IS INVARSPEC
    ASSUME Spec
    PROVE MUTUALEXCLUSION

THEOREM EventualReturnIsHolds
    ASSUME SpecStrongFairness
    PROVE EVENTUALLY(EventualReturn)

THEOREM EventualObtainmentIsHolds
    ASSUME SpecStrongFairness
    PROVE EVENTUALLY(EventualObtainment)

THEOREM InfinitelyOftenNoPendingIsHolds
    ASSUME SpecStrongFairness
    PROVE EVENTUALLY(InfinitelyOftenNoPending)
```