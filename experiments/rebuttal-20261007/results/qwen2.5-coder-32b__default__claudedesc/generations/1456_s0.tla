------------------------------- MODULE SubsetTest -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    (* No constants needed for this specification *)

VARIABLES x, y

Init == /\ x \subseteq {1, 2}
        /\ y = {1, 2, 3}

Next == /\ y' = y
        /\ x' \subseteq y'

Spec == Init /\ [][Next]_<<x, y>>

TypeOK == x \subseteq {1, 2, 3}

Inv == /\ (EXISTS x': x' \subseteq {1} /\ x' \subseteq y)
       /\ y = {1, 2, 3}

FullSet == x = {1, 2, 3}
GainThree == \/ 3 \in x'
             \/ 3 \notin x /\ 3 \in x'

PossibleCounts ==
    /\ _POSSIBLE{st: FullSet} = 8
    /\ _POSSIBLE{tr: GainThree} = 16

=============================================================================