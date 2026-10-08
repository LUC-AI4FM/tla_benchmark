MODULE SubsetCheck

EXTENDS Naturals, Integers, SETS

VARIABLE b

Init == 
    /\ b = TRUE

Next ==
    /\ b' = (
        {1,2} ⊆ {1,2,3}
        ∧ ¬({4} ⊆ {5})
        ∧ { i \in 1 .. 5 : TRUE } ⊆ { j \in 0 .. 10 : TRUE }
        ∧ ¬( { i \in 6 .. 8 : TRUE } ⊆ { j \in 0 .. 5 : TRUE } )
        ∧ {0} ⊆ NAT
        ∧ ¬({-1} ⊆ NAT)
        ∧ {-5} ⊆ INT
    )

Spec == Init /\ [][Next]_b

Invariant == b = TRUE ∧ b \in BOOLEAN