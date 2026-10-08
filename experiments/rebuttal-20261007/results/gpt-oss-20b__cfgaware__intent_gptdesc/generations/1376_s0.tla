------------------------------ MODULE GrowingRepo ------------------------------
EXTENDS Temporal

CONSTANTS Items   \* finite set of possible items

VARIABLE items

(* --- State Invariant ----------------------------------------------------- *)
Init == 
    /\ items = {}

Add(item) ==
    /\ item \in Items
    /\ item \notin items
    /\ items' = items \cup {item}

Next ==
    \/ \E item \in Items : Add(item)

Spec == Init /\ [][Next]_items

(* --- Safety Properties --------------------------------------------------- *)
SafetyInvariant == items \subseteq Items
MonotonicityInvariant == [] (items' \supseteq items)

(* --- Liveness Properties ------------------------------------------------- *)
EventuallyAdd(i) == []<> (i \in items)
AllEventual == \A i \in Items : EventuallyAdd(i)

Fairness == WF_vars(Next)

=============================================================================