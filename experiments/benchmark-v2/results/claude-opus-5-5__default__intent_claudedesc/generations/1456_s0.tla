---- MODULE SubsetEqEnabled ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a, b, c

VARIABLES x, y

vars == <<x, y>>

Universe == {a, b, c}

Init ==
    /\ x \in SUBSET {a, b}
    /\ y = Universe

Next ==
    /\ y' = y
    /\ x' \subseteq y'

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \subseteq Universe
    /\ y = Universe

EnabledSingleton ==
    ENABLED (x' \subseteq {a} /\ y' = y)

Inv ==
    /\ x \subseteq Universe
    /\ EnabledSingleton

-----------------------------------------------------------------------------
_POSSIBLE_Full ==
    /\ x' = Universe
    /\ TLCSet(1, TLCGet(1) + 1)

_POSSIBLE_Gain ==
    /\ c \notin x
    /\ c \in x'
    /\ TLCSet(2, TLCGet(2) + 1)

InitCounters ==
    /\ TLCSet(1, 0)
    /\ TLCSet(2, 0)

CountingInit ==
    /\ InitCounters
    /\ Init

CountingNext ==
    /\ Next
    /\ \/ _POSSIBLE_Full
       \/ ~(x' = Universe)
    /\ \/ _POSSIBLE_Gain
       \/ ~(c \notin x /\ c \in x')

CountingSpec == CountingInit /\ [][CountingNext]_vars

PostCondition ==
    /\ TLCGet(1) = 8
    /\ TLCGet(2) = 16

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM CountingSpec => []TypeOK
=============================================================================