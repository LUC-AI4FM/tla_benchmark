--------------------------- MODULE TinyState ----------------------------
EXTENDS TLC

VARIABLES x, y

Init == /\ x \in SUBSET {1, 2, 3}
        /\ y \in SUBSET {1, 2, 3}
        /\ x \subseteq y

Next == /\ y' = y
        /\ x' \subseteq y'

TypeOK == /\ x \in SUBSET {1, 2, 3}
          /\ y \in SUBSET {1, 2, 3}

Inv == x \subseteq y

FullSet == (x = {1, 2, 3})

GainThree == /\ 3 \in y
            /\ 3 \notin x
            /\ 3 \in x'

FullSetCount == TLCGet("FullSet")
GainThreeCount == TLCGet("GainThree")

ASSERT FullSetCount >= 0
ASSERT GainThreeCount >= 0

=============================================================================