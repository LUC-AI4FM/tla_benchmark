---------------------------- MODULE SubsetCheck ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next ==
    /\ b' \in BOOLEAN
    /\ b' = (SUBSET {x \in 1..5 : x > 0} \subseteq SUBSET {y \in 1..10 : y < 20})
       /\ (\neg (SUBSET {a, b, c} \subseteq SUBSET {b, c, d}))
       /\ (SUBSET Int \subseteq SUBSET Nat)
       /\ (\neg (SUBSET {x \in Int : x > 0} \subseteq SUBSET {y \in Nat : y < 0}))

Spec ==
    /\ Init
    /\ [][Next]_<<b>>

Inv == b = TRUE /\ b \in BOOLEAN

=============================================================================