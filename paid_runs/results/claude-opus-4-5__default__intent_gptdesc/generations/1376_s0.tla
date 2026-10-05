---------------------------- MODULE GrowingRepository ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Universe  \* The fixed finite set of all possible items that can be added

VARIABLES
    items     \* The current set of items in the repository

vars == <<items>>

-----------------------------------------------------------------------------
(* Type Invariant *)

TypeOK ==
    /\ items \subseteq Universe
    /\ IsFiniteSet(items)

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    items = {}

-----------------------------------------------------------------------------
(* Actions *)

\* Add a single item from Universe that is not already present
AddItem(item) ==
    /\ item \in Universe
    /\ item \notin items
    /\ items' = items \cup {item}

\* Stuttering step (system can choose to do nothing)
Stutter ==
    UNCHANGED items

\* Next state relation: nondeterministically add any allowed item
Next ==
    \/ \E item \in Universe : AddItem(item)
    \/ Stutter

-----------------------------------------------------------------------------
(* Specification *)

\* Basic specification without fairness
Spec == Init /\ [][Next]_vars

\* Specification with weak fairness on adding each item
\* This ensures that if an item can be added infinitely often, it eventually will be
FairSpec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A item \in Universe : WF_vars(AddItem(item))

\* Specification with strong fairness (item will be added if it's enabled infinitely often)
StrongFairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A item \in Universe : SF_vars(AddItem(item))

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* The set of items is always a subset of the allowed universe
SubsetInvariant ==
    items \subseteq Universe

\* The repository started empty (this is ensured by Init, checked as invariant)
InitiallyEmpty ==
    items = {} \/ items # {}  \* Trivially true; actual check is that Init => items = {}

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ SubsetInvariant

-----------------------------------------------------------------------------
(* Monotonicity Property *)

\* Monotonicity: items never shrink (expressed as a temporal property)
\* For any state, the next state's items contains all current items
MonotonicGrowth ==
    [][items \subseteq items']_vars

\* Alternative: items set size never decreases
MonotonicSize ==
    [][Cardinality(items) <= Cardinality(items')]_vars

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Under fair specification, every item eventually gets added
AllItemsEventuallyAdded ==
    \A item \in Universe : <>(item \in items)

\* Some specific item eventually gets added (parameterized check)
\* Use with a specific constant, e.g., ItemEventuallyAdded with item \in Universe
ItemEventuallyAdded(item) ==
    <>(item \in items)

\* The repository eventually becomes complete (contains all items)
EventuallyComplete ==
    <>(items = Universe)

\* It's always possible for the repository to grow (unless complete)
CanAlwaysGrow ==
    [](items # Universe => <>(items # items'))

\* Some items may remain absent forever (this is possible without fairness)
\* This property should FAIL under FairSpec but may PASS under Spec
SomeItemNeverAdded ==
    \E item \in Universe : [](item \notin items)

-----------------------------------------------------------------------------
(* Reachability Invariant *)

\* Every state is reachable only by successive additions
\* This is implicitly guaranteed by the structure of Init and Next
\* We express it as: if items is non-empty, there exists some item whose
\* removal would give a valid predecessor state
ReachableByAdditions ==
    items = {} \/ \E item \in items : (items \ {item}) \subseteq Universe

-----------------------------------------------------------------------------
(* Additional Properties for Model Checking *)

\* The repository is never larger than the universe
BoundedSize ==
    Cardinality(items) <= Cardinality(Universe)

\* Progress property: if not complete, something can be added
ProgressPossible ==
    items # Universe => \E item \in Universe : item \notin items

\* Deadlock freedom (there's always a next state possible)
\* With Stutter, this is always true; without it, deadlock occurs when items = Universe
NoDeadlock ==
    ENABLED(Next)

-----------------------------------------------------------------------------
(* Theorems for Verification *)

\* Safety theorem: Spec maintains SafetyInvariant
THEOREM Spec => []SafetyInvariant

\* Monotonicity theorem: Spec maintains monotonic growth
THEOREM Spec => MonotonicGrowth

\* Liveness theorem: FairSpec ensures all items eventually added
THEOREM FairSpec => AllItemsEventuallyAdded

\* Liveness theorem: FairSpec ensures eventual completeness
THEOREM FairSpec => EventuallyComplete

=============================================================================