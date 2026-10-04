---------------------------- MODULE Specification ----------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS S1, S2, S3

Universe == {S1, S2, S3}
TwoElementSet == {S1, S2}
Singleton == {S1}

VARIABLES x, y

vars == <<x, y>>

TypeOK == x \subseteq Universe /\ y \subseteq Universe

Init == 
    /\ x \in SUBSET TwoElementSet
    /\ y = Universe

Next ==
    /\ y' = y
    /\ x' \subseteq y'

NextSingleton ==
    /\ y' = y
    /\ x' \subseteq Singleton

EnabledInv == ENABLED NextSingleton

Inv == TypeOK /\ EnabledInv

XEqualsUniverse == x = Universe

S1NewlyGained == S1 \in x' /\ S1 \notin x

XEqualsUniverse_POSSIBLE == XEqualsUniverse

S1NewlyGained_POSSIBLE == S1NewlyGained

Alias == [
    x |-> x,
    y |-> y,
    XEqualsUniverse |-> XEqualsUniverse,
    EnabledNextSingleton |-> ENABLED NextSingleton
]

Postcondition ==
    /\ TLCGet("stats").distinct >= 0

Spec == Init /\ [][Next]_vars

=============================================================================