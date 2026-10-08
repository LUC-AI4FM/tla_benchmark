------------------------------- MODULE GrowingRepository -------------------------------

CONSTANTS
    UNIVERSE \* The set of all possible items that can be added to the repository

VARIABLES
    repo \* The current set of items in the repository

Init == repo = {}

Next ==
    \/ /\ \E item \in (UNIVERSE \ repo) : repo' = repo \cup {item}
       /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<repo>>

\* Invariants
Inv1 == repo \subseteq UNIVERSE \* The repository is a subset of the universe
Inv2 == Cardinality(repo) = Cardinality({x \in repo : x \in UNIVERSE}) \* No duplicates beyond set semantics

TypeInvariant == Inv1 /\ Inv2

\* Liveness: Eventually all items in the universe are added (optional)
AllItemsAdded == <>(repo = UNIVERSE)

\* Liveness: Fairness for each item to be added at least once (optional)
FairAdd(item) == WF_(<<repo>>, \E i \in (UNIVERSE \ repo) : repo' = repo \cup {i})

=============================================================================