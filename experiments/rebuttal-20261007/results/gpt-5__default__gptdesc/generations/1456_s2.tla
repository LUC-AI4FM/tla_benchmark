----------------------------- MODULE TinySetMachine -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    FullSetExpected, \* expected number of states where FullSet holds (for TLC)
    GainThreeExpected \* expected number of transitions where GainThree holds (for TLC)

VARIABLES x, y

vars == << x, y >>

Init ==
    /\ x \in SUBSET {1, 2, 3}
    /\ y \in SUBSET {1, 2, 3}
    /\ x \subseteq y

Next ==
    /\ y' = y
    /\ x' \subseteq y'

\* Named predicates
FullSet ==
    x = {1, 2, 3}

GainThree ==
    /\ ~(3 \in x)
    /\ 3 \in x'

\* Safety invariant (type and subset relation are preserved)
TypeInv ==
    /\ x \subseteq {1, 2, 3}
    /\ y \subseteq {1, 2, 3}
    /\ x \subseteq y

\* TLC metadata checks for named predicates (for use with TLCGet)
CoverageAssertions ==
    /\ TLCGet("StatePredicateCount", "FullSet") = FullSetExpected
    /\ TLCGet("ActionPredicateCount", "GainThree") = GainThreeExpected

Spec ==
    Init /\ [][Next]_vars
=============================================================================