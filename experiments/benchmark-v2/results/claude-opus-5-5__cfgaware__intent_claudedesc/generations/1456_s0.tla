---------------------------- MODULE SubsetEnabled ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Universe == {1, 2, 3}

Init ==
    /\ x \subseteq {1, 2}
    /\ y = {1, 2, 3}

Next ==
    /\ y' = y
    /\ x' \subseteq y'

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \subseteq Universe
    /\ y = Universe

Inv ==
    ENABLED (/\ y' = y
             /\ x' \subseteq {1})

\* State predicates whose satisfying (successor) states TLC counts.
FullSet == x = {1, 2, 3}

GainThree == (3 \notin x) /\ (3 \in x')

_POSSIBLE == <<FullSet, GainThree>>

\* TLC explores 8 reachable states and generates 8 * 8 = 64 successor pairs.
\* FullSet holds for the 8 pairs whose source state is {1,2,3}.
\* GainThree holds for the 4 * 4 = 16 pairs that go from a state without 3
\* to a state with 3.
PossibleCounts ==
    TLCGet("possible") = <<8, 16>>

=============================================================================