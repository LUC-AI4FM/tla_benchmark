MODULE GrowingSet
VARIABLES S

Init == S = {}

Next == \E x \in {1, 2} : S' = S \cup {x}

Spec == Init /\ [][Next]_S