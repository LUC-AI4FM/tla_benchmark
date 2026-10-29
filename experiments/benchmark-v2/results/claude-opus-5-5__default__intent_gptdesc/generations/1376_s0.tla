------------------------------ MODULE GrowingRepository ------------------------------
(***************************************************************************)
(* A growing repository of distinct data items. The repository starts     *)
(* empty. At any step, any allowed item not already present may be added. *)
(* Items are never removed or modified. Additions interleave in any       *)
(* order, and some items may never be added.                              *)
(*                                                                         *)
(* The variable history is an auxiliary variable. It records the order   *)
(* in which items were added, so the spec can state that every reachable *)
(* state comes from successive additions of single allowed items.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Items,        \* fixed finite universe of possible data items
    TargetItem    \* a distinguished item used for item-specific liveness checks

ASSUME ItemsFinite  == IsFiniteSet(Items)
ASSUME TargetInItems == TargetItem \in Items

VARIABLES
    repo,     \* the set of items currently in the repository
    history   \* sequence of items in the order they were added (auxiliary)

vars == << repo, history >>

-----------------------------------------------------------------------------
(* Helper operators *)

Range(s) == { s[k] : k \in DOMAIN s }

NoDuplicates(s) ==
    \A j, k \in DOMAIN s : (j # k) => (s[j] # s[k])

-----------------------------------------------------------------------------
(* Initial state: the repository is empty *)

Init ==
    /\ repo = {}
    /\ history = << >>

-----------------------------------------------------------------------------
(* Actions *)

\* Add a single allowed item that is not yet present.
Add(i) ==
    /\ i \in Items
    /\ i \notin repo
    /\ repo' = repo \cup {i}
    /\ history' = Append(history, i)

\* Once every item is present, the system idles. This avoids reporting a
\* deadlock. It changes no variable, so it is a stuttering step.
Saturated ==
    /\ repo = Items
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Items : Add(i)
    \/ Saturated

-----------------------------------------------------------------------------
(* Specifications *)

\* Safety-only specification. It has no fairness, so the system may stutter
\* forever, and some items (possibly all of them) may never be added.
Spec == Init /\ [][Next]_vars

\* Fair specification. Weak fairness on adding each individual item
\* guarantees that every item is eventually added.
FairSpec ==
    /\ Spec
    /\ \A i \in Items : WF_vars(Add(i))

\* Specification with fairness only on the distinguished TargetItem.
\* It guarantees that TargetItem is eventually added. Other items may
\* remain absent forever.
TargetFairSpec ==
    /\ Spec
    /\ WF_vars(Add(TargetItem))

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ repo \subseteq Items
    /\ history \in Seq(Items)

\* The repository is always a subset of the allowed universe.
SubsetOfUniverse == repo \subseteq Items

\* No duplicates: each item was added at most once, so the number of
\* recorded additions equals the number of distinct items present.
NoDuplicateAdds ==
    /\ NoDuplicates(history)
    /\ Len(history) = Cardinality(repo)

\* Reachability: every state is obtained from the empty state by successive
\* additions of single allowed items. The history is exactly such a
\* sequence of additions, and replaying it yields the current repository.
ReachableBySingleAdditions ==
    /\ history \in Seq(Items)
    /\ Range(history) = repo
    /\ NoDuplicates(history)
    /\ \A k \in 0..Len(history) :
           Range(SubSeq(history, 1, k)) \subseteq Items

\* Size bound that follows from the subset property.
BoundedSize == Cardinality(repo) <= Cardinality(Items)

\* The initial state is empty. Checked as a temporal formula, it holds of
\* the first state of every behavior.
InitiallyEmpty == (repo = {} /\ history = << >>)

\* The repository is empty exactly when no additions have occurred.
EmptyIffNoHistory == (repo = {}) <=> (history = << >>)

Inv ==
    /\ TypeOK
    /\ SubsetOfUniverse
    /\ NoDuplicateAdds
    /\ ReachableBySingleAdditions
    /\ BoundedSize
    /\ EmptyIffNoHistory

-----------------------------------------------------------------------------
(* Temporal safety properties: monotonicity *)

\* Action-level monotonicity: the repository never shrinks.
Monotonic == [][repo \subseteq repo']_vars

\* No item is ever removed once present.
NoRemoval == [][\A i \in repo : i \in repo']_vars

\* Each step adds at most one item, and that item is an allowed one.
SingleItemSteps ==
    [][ \/ repo' = repo
        \/ \E i \in Items \ repo : repo' = repo \cup {i} ]_vars

\* History is append-only.
HistoryAppendOnly ==
    [][ /\ Len(history') >= Len(history)
        /\ SubSeq(history', 1, Len(history)) = history ]_vars

\* State-level formulation: once an item is present, it stays present forever.
Permanence == \A i \in Items : [](i \in repo => [](i \in repo))

\* The initial state is empty (temporal formula, evaluated on the first state).
InitEmptyProperty == InitiallyEmpty

-----------------------------------------------------------------------------
(* Liveness properties *)

\* A specific item is eventually added.
\* Holds under FairSpec and TargetFairSpec. Fails under Spec.
EventuallyTargetAdded == <>(TargetItem \in repo)

\* Every permitted item eventually appears.
\* Holds under FairSpec. Fails under Spec and, in general, under TargetFairSpec.
EventuallyAllAdded == \A i \in Items : <>(i \in repo)

\* The repository eventually becomes saturated and stays saturated.
EventuallySaturated == <>[](repo = Items)

\* Every item, once added, is permanently present (a stability property).
AddedStaysAdded == \A i \in Items : (i \in repo) ~> [](i \in repo)

\* "Some items may remain absent." Under the unfair Spec, model-checking
\* the property below produces a counterexample. That counterexample is a
\* behavior in which TargetItem is never added, which confirms that
\* absence is possible. Under FairSpec this property holds.
TargetNotForeverAbsent == ~[](TargetItem \notin repo)

\* Conversely, the claim that the target is always absent is violated
\* as soon as it is added. Checking it shows that addition is reachable.
TargetAlwaysAbsent == [](TargetItem \notin repo)

-----------------------------------------------------------------------------
(* Theorems (documentation of intended verification results) *)

THEOREM Spec => []Inv
THEOREM Spec => Monotonic /\ NoRemoval /\ SingleItemSteps /\ HistoryAppendOnly
THEOREM Spec => InitEmptyProperty
THEOREM FairSpec => EventuallyAllAdded /\ EventuallySaturated
THEOREM TargetFairSpec => EventuallyTargetAdded
=============================================================================