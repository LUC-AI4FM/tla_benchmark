MODULE SubsetInvariant
EXTENDS SETS

VARIABLE b

Init == 
  b = TRUE

Next ==
  b' = ({1,2} \subseteq 1..3) /\ (1..5 \subseteq Int) /\
       ~( {1,2,4} \subseteq {1,2,3} ) /\ (0..5 \subseteq Nat) /\ (Nat \subseteq Int)

Inv == (b \in Boolean) /\ (b = TRUE)

Spec == Init /\ []Next /\ [](Inv)