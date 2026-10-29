---------------------------- MODULE GrowingSet ----------------------------
(***************************************************************************)
(* A growing repository of distinct data items. The repository starts      *)
(* empty. At each step one item from the fixed finite universe Data is     *)
(* added nondeterministically. Items are never removed or modified.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Data

ASSUME IsFiniteSet(Data)

VARIABLE items

vars == <<items>>

-----------------------------------------------------------------------------
TypeOK == items \subseteq Data

Init == items = {}

(* Add a single allowed item. Re-adding an item already present leaves the
   set unchanged under set semantics, so we only add absent items.         *)
Add(d) ==
    /\ d \notin items
    /\ items' = items \cup {d}

(* Once every item is present, the system stutters, so a finished
   repository is not reported as a deadlock.                               *)
Done ==
    /\ items = Data
    /\ UNCHANGED items

Next == (\E d \in Data : Add(d)) \/ Done

Spec == Init /\ [][Next]_vars

(* Fairness variant: every item that can be added eventually is added.     *)
FairSpec == Spec /\ \A d \in Data : WF_vars(Add(d))

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

(* The repository is always a subset of the allowed universe.              *)
SubsetOfUniverse == items \subseteq Data

(* The size is bounded by the universe. Duplicates cannot occur under set
   semantics.                                                              *)
BoundedSize == Cardinality(items) <= Cardinality(Data)

(* Initial-state property: the repository starts empty.                    *)
InitEmpty == items = {}

(* Each step either adds exactly one allowed item or changes nothing.      *)
SingleAdditionStep ==
    [][ \/ \E d \in Data : d \notin items /\ items' = items \cup {d}
        \/ items' = items ]_vars

(* Monotonicity: the set of items never shrinks.                           *)
Monotonic == [][items \subseteq items']_vars

(* Every item that is added stays present permanently.                     *)
Permanence == \A d \in Data : [](d \in items => [](d \in items))

-----------------------------------------------------------------------------
(* Liveness properties (check under FairSpec)                              *)

(* Each permitted item eventually appears.                                 *)
EventuallyEachAdded == \A d \in Data : <>(d \in items)

(* Eventually the repository holds the entire universe.                    *)
EventuallyComplete == <>(items = Data)

(* Once complete, the repository stays complete.                           *)
StableComplete == <>[](items = Data)

(* Under Spec alone (no fairness), some items may remain absent forever.
   Checking this negated property is expected to fail when Data # {}.      *)
SomeItemMayStayAbsent == \E d \in Data : [](d \notin items)

=============================================================================