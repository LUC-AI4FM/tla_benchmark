------------------------------ MODULE TinySM ------------------------------

DOMAIN == {1, 2, 3}

VARIABLES x, y

FullSet == x = DOMAIN
(* @named FullSet *)

GainThree == (3 ∈ x') /\ ~(3 ∈ x)
(* @named GainThree *)

Init ==
    /\ x ∈ SUBSET DOMAIN
    /\ y ∈ SUBSET DOMAIN

Next ==
    /\ y' = y
    /\ x' ⊆ y

FullSetCountCheck == (TLCGet("FullSet") = 1)
GainThreeCountCheck == (TLCGet("GainThree") = 2)

Spec == Init /\ [][Next]_<<x,y>> 
          /\ FullSetCountCheck
          /\ GainThreeCountCheck

=============================================================================