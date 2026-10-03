---------------------------- MODULE spec ----------------------------

EXTENDS Integers, TLC

VARIABLES x, y

TypeOK == /\ x \subseteq {1, 2, 3}
          /\ y \subseteq {1, 2, 3}

Init == /\ x \in SUBSET {1, 2, 3}
        /\ y \in SUBSET {1, 2, 3}

Next == /\ y' = y
        /\ x' \in SUBSET y'

FullSet == x = {1, 2, 3}

GainThree == /\ 3 \notin x
             /\ 3 \in x'

Inv == /\ TypeOK
       /\ x \subseteq {1, 2, 3}
       /\ y \subseteq {1, 2, 3}

CheckCounts == 
    /\ TLCGet("stats").states.distinct > 0
    /\ TRUE

=======================================================================