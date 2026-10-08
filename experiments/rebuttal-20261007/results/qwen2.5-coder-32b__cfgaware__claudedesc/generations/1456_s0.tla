---- MODULE SubsetConstraintTest ----

VARIABLES x, y

CONSTANTS
    (* No additional constants needed for this specification *)

Init == /\ x \subseteq {1, 2}
        /\ y = {1, 2, 3}

Next == \/ /\ x' \subseteq y'
          /\ y' = y

TypeOK == x \subseteq {1, 2, 3}

Inv == /\ \E x'' \in SUBSET {1} : x'' \subseteq y
       /\ y = {1, 2, 3}

FullSet == x = {1, 2, 3}
GainThree == 3 \in x'

PossibleCounts ==
    /\ _POSSIBLE{ s \in S_0 : FullSet } = 8
    /\ _POSSIBLE{ t \in T_0 : GainThree } = 16

====