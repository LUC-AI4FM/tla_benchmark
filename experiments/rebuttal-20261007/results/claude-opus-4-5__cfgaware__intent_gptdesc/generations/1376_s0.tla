---------------------------- MODULE specification ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Items

VARIABLES items

vars == <<items>>

TypeOK == items \subseteq Items

Init == items = {}

AddItem(i) == 
    /\ i \in Items
    /\ i \notin items
    /\ items' = items \cup {i}

Add == \E i \in Items : AddItem(i)

Stutter == UNCHANGED items

Next == Add \/ Stutter

Spec == Init /\ [][Next]_vars

FairSpec == Init /\ [][Next]_vars /\ WF_vars(Add)

StrongFairSpec == Init /\ [][Next]_vars /\ SF_vars(Add)

Safety == items \subseteq Items

Monotonicity == [][items \subseteq items']_vars

NoDuplicates == Cardinality(items) = Cardinality(items)

InitEmpty == items = {}

Invariant == TypeOK /\ Safety

EventuallyAllItems == <>(items = Items)

EventuallySomeItem == \A i \in Items : <>(i \in items)

ItemMayRemainAbsent == \E i \in Items : []~(i \in items)

CanAddAnyItem == \A i \in Items : (i \notin items) => ENABLED AddItem(i)

ReachableByAdditions == 
    /\ items \subseteq Items
    /\ Cardinality(items) \in 0..Cardinality(Items)

NeverShrinks == [][\A i \in items : i \in items']_vars

LivenessProperty == []<>ENABLED Add => <>(\E i \in Items : i \in items)

=============================================================================