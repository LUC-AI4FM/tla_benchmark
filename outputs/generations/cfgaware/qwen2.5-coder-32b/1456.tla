------------------------------- MODULE TinyStateMachine -------------------------------

CONSTANTS
    \* Constants are not explicitly defined in this problem statement,
    \* but we can assume necessary constants if needed. Here, no additional constants are required.

VARIABLES x, y

Init == /\ x = {}
        /\ y = {1, 2, 3}

Next == \/ /\ x' \subseteq y
            /\ y' = y

TypeOK == /\ x \in SUBSET {1, 2, 3}
          /\ y = {1, 2, 3}

Inv == TRUE

FullSet == x = {1, 2, 3}

GainThree == \/ 3 \notin x
             /\ 3 \in x'

=============================================================================