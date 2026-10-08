MODULE SubsetSpec
EXTENDS Naturals, Integers

VARIABLE b

Init ==
    b = TRUE

Next ==
    b' =
        ( {1,2} ⊆ {1,2,3} ) /\
        (~({4,5} ⊆ {1,2,3})) /\
        ( {1..5} ⊆ {1..10} ) /\
        (~({6..9} ⊆ {1..5})) /\
        ( {0,1,2} ⊆ Nat ) /\
        (~({-1,-2} ⊆ Nat)) /\
        ( {-3 .. 3} ⊆ Int ) /\
        (~({4..10} ⊆ {0..3}))

Inv ==
    b = TRUE /\ b ∈ {TRUE, FALSE}

Spec ==
    Init /\ [][Next]_<<b>> /\ Inv