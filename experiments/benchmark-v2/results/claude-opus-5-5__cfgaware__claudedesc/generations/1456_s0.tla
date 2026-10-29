---------------------------- MODULE SubsetEqPrimed ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x \subseteq {1, 2}
    /\ y = {1, 2, 3}

Next ==
    /\ y' = y
    /\ x' \subseteq y'

Spec == Init /\ [][Next]_vars

TypeOK == x \subseteq {1, 2, 3}

Inv ==
    /\ ENABLED (x' \subseteq {1})
    /\ y = {1, 2, 3}

\* State predicate: y holds the full set {1, 2, 3}.
\* It is true in every reachable state, and there are 8 of them.
FullSet == y = {1, 2, 3}

\* Transition predicate: the element 3 is added to x.
\* There are 4 source states without 3 and 4 target states with 3,
\* which gives 16 transitions.
GainThree == 3 \notin x /\ 3 \in x'

\* Predicates whose satisfying states and transitions TLC counts.
_POSSIBLE == {"FullSet", "GainThree"}

\* Postcondition: checks the counts that TLC recorded.
PossibleCounts ==
    LET p == TLCGet("possible")
    IN  /\ p["FullSet"] = 8
        /\ p["GainThree"] = 16

=============================================================================