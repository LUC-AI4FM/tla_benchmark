----------------------------- MODULE GrowingRepo -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
A repository that grows by nondeterministically adding distinct items
from a fixed finite universe UNIV. Once added, an item remains forever.
The system begins empty. Steps add exactly one new allowed item.
Stuttering steps are allowed via [][Next]_vars.
Fairness is optional and controlled by the constant MustAdd.
*)

CONSTANTS
    UNIV,      \* Finite set of all permitted items
    MustAdd    \* Subset of UNIV whose items are required to eventually be added (optional)

ASSUME IsFiniteSet(UNIV) /\ MustAdd \subseteq UNIV

VARIABLES
    Items,   \* set of items currently present
    Hist     \* sequence of items, in the order they were added (no duplicates)

vars == << Items, Hist >>

Init ==
    /\ Items = {}
    /\ Hist = << >>

Add(i) ==
    /\ i \in UNIV \ Items
    /\ Items' = Items \cup { i }
    /\ Hist'  = Append(Hist, i)

Next ==
    \E i \in UNIV \ Items : Add(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

(***************************************************************************)
(* Safety and well-formedness invariants                                   *)
(***************************************************************************)

Elems(s) == { s[k] : k \in 1..Len(s) }

NoDups(s) == Cardinality(Elems(s)) = Len(s)

TypeInv ==
    Items \subseteq UNIV

HistInv ==
    /\ Items = Elems(Hist)
    /\ NoDups(Hist)
    /\ \A k \in 1..Len(Hist) : Hist[k] \in UNIV

Safety == [](TypeInv /\ HistInv)

(***************************************************************************)
(* Monotonicity (no removals)                                              *)
(***************************************************************************)

Monotone == Items \subseteq Items'
AlwaysMonotone == []Monotone

(***************************************************************************)
(* Single-add step characterization (action-level sanity)                  *)
(***************************************************************************)

AddStep == \E i \in UNIV \ Items : /\ Items' = Items \cup { i } /\ Hist' = Append(Hist, i)
AddOnly == [](Next => AddStep)

(***************************************************************************)
(* Optional fairness and liveness statements                               *)
(***************************************************************************)

\* Per-item weak fairness: if Add(i) stays enabled, it will eventually occur.
Fairness ==
    /\ \A i \in MustAdd : WF_vars(Add(i))

\* Liveness guarantees implied by the above fairness (not part of Spec unless checked):
Guarantee_MustAdd ==
    \A i \in MustAdd : <> (i \in Items)

\* Stronger (optional) liveness: eventually every permitted item appears.
EventuallyAll ==
    \A i \in UNIV : <> (i \in Items)

\* Optional per-item liveness to check for a particular j \in UNIV:
EventuallyAdded(j) == <> (j \in Items)

\* Optional "remain absent" property for a particular j \in UNIV:
AlwaysAbsent(j) == [](j \in UNIV => j \notin Items)

=============================================================================