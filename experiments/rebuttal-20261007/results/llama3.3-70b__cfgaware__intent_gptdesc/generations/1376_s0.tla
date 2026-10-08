---------------------------- MODULE GrowingRepository ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Universe
VARIABLE repository

Init == repository = {}

AddItem(item) == 
  item \in Universe /\ 
  repository' = repository \cup {item}

Next == \E item \in Universe : AddItem(item)

Spec == Init /\ [][Next]_repository

THEOREM Spec => []Init
THEOREM Spec => []repository \subseteq Universe
THEOREM Spec => <<repository>> \in [Universe -> Nat]
THEOREM Spec => repository \in [Universe -> Bool]

Fairness == \A item \in Universe : <>AddItem(item)

EventualAddition == \A item \in Universe : []<>item \in repository

Monotonicity == repository \subseteq repository'

Inv1 == Init
Inv2 == repository = {}
Inv3 == repository \subseteq Universe

=============================================================================