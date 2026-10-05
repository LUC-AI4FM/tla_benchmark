---------------------------- MODULE subset_test ----------------------------
EXTENDS Integers, TLC, FiniteSets

VARIABLES x, y

Init ==
    /\ x \in SUBSET {1, 2}
    /\ y = {1, 2, 3}

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

TypeOK ==
    x \subseteq {1, 2, 3}

Inv ==
    /\ ENABLED (x' \subseteq {1})
    /\ y = {1, 2, 3}

FullSet ==
    x = {1, 2, 3}

GainThree ==
    /\ 3 \notin x
    /\ 3 \in x'

FullSet_POSSIBLE ==
    FullSet

GainThree_POSSIBLE ==
    GainThree

PossibleCounts ==
    /\ TLCGet("stats").states.distinct = 8
    /\ TRUE

vars == <<x, y>>

Spec == Init /\ [][Next]_vars

=============================================================================