MODULE TwoProcessLock
EXTENDS Naturals, TLC

CONSTANTS Proc

VARIABLE owner, loc

(*--------------------------------------------------------------------*)
(* Type invariants *)
TypeInvariant ==
  /\ owner ∈ Proc \/ owner = 0
  /\ ∀ i ∈ Proc : loc[i] ∈ {"NC", "L1", "CS", "L2"}

(*--------------------------------------------------------------------*)
(* Initial state *)
Init ==
  /\ owner = 0
  /\ ∀ i ∈ Proc : loc[i] = "NC"

(*--------------------------------------------------------------------*)
(* Next-state relation *)
Next ==
  \/ (* Process 1: NC -> L1 *)
     (loc[1] = "NC" /\ loc' = [loc EXCEPT ![1] = "L1"] /\ owner' = owner)
  \/ (* Process 2: NC -> L2 *)
     (loc[2] = "NC" /\ loc' = [loc EXCEPT ![2] = "L2"] /\ owner' = owner)
  \/ (* Process 1 acquires lock *)
     (loc[1] = "L1" /\ owner = 0
      /\ loc' = [loc EXCEPT ![1] = "CS"]
      /\ owner' = 1)
  \/ (* Process 2 acquires lock *)
     (loc[2] = "L2" /\ owner = 0
      /\ loc' = [loc EXCEPT ![2] = "CS"]
      /\ owner' = 2)
  \/ (* Process 1 releases lock *)
     (loc[1] = "CS"
      /\ loc' = [loc EXCEPT ![1] = "NC"]
      /\ owner' = 0)
  \/ (* Process 2 releases lock *)
     (loc[2] = "CS"
      /\ loc' = [loc EXCEPT ![2] = "NC"]
      /\ owner' = 0)

(*--------------------------------------------------------------------*)
(* Safety invariant: mutual exclusion and correct ownership *)
MutualExclusion ==
  ∀ i,j ∈ Proc : (loc[i] = "CS" /\ loc[j] = "CS") ⇒ i=j

OwnerMatches ==
  owner ≠ 0 ⇒ (∃! i ∈ Proc : owner=i /\ loc[i]="CS")

Invariant == MutualExclusion /\ OwnerMatches

(*--------------------------------------------------------------------*)
(* Liveness property: if process 1 is waiting, it eventually enters CS *)
Liveness ==
  [](loc[1] = "L1" ⇒ <> loc[1] = "CS")

(*--------------------------------------------------------------------*)
(* Specification *)
Spec == Init /\ [][Next]_<<owner, loc>> /\ []TypeInvariant

(*--------------------------------------------------------------------*)
THEOREM Spec ⊆ []Invariant
THEOREM Spec ⊆ Liveness

===============================================================================