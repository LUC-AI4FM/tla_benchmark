------------------------------ MODULE RandomSubsetTest ------------------------------
EXTENDS Randomization

VARIABLE x

S == 1..9
T == 1..10

Init ==
    /\ x \in RandomSubset([S -> T], 1000)

Next ==
    UNCHANGED <<x>>

Spec ==
    Init /\ [][Next]_<<x>>