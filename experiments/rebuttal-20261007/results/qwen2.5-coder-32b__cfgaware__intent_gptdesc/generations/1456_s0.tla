------------------------------- MODULE SubsetSystem -------------------------------

CONSTANTS Universe

VARIABLES subset

ASSUME Universe = {1, 2, 3}

Init == /\ subset \subseteq Universe
        /\ subset /= Universe

Next == \E newSubset \in SUBSET Universe :
            \/ /\ newSubset = subset
               /\ \/ \E x \in Universe - subset : newSubset' = subset \cup {x}
                  \/ \E x \in subset : newSubset' = subset - {x}
            \/ newSubset' = newSubset

TypeOK == /\ subset \subseteq Universe

Inv == /\ TypeOK
       /\ Universe = {1, 2, 3}

Spec == Init /\ [][Next]_<<subset>>

FullSetReached == \E s \in States : s.subset = Universe

ElementGained(element) == \E t \in Transitions :
    element \notin t.state.subset
    /\ element \in t.state'.subset

=============================================================================