---------------------------- MODULE SubsetEnabled ----------------------------
EXTENDS Integers, TLC, FiniteSets

CONSTANTS a, b, c

VARIABLES x, y

Universe == {a, b, c}
SmallSet == {a, b}
Singleton == {a}

TypeOK == x \subseteq Universe /\ y = Universe

Init == 
    /\ x \in SUBSET SmallSet
    /\ y = Universe

Next ==
    /\ y' = y
    /\ x' \in SUBSET y

EnabledSingletonSubset == ENABLED (x' \in SUBSET Singleton /\ y' = y)

AlwaysEnabled == EnabledSingletonSubset

XIsFullSet == x = Universe

CGainedC == c \in x' /\ c \notin x

XIsFullSet_POSSIBLE == TLCGet("stats").traces

CGainedC_POSSIBLE == TLCGet("stats").traces

Inv1 == x \subseteq Universe

Inv2 == EnabledSingletonSubset

PostCondition ==
    LET stats == TLCGet("stats")
    IN /\ Print(<<"Distinct states">>, TRUE)
       /\ TRUE

Spec == Init /\ [][Next]_<<x, y>>
=============================================================================