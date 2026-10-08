------------------------------ MODULE SubsetSpec ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Elem1, Elem2, Elem3

VARIABLES
    X, Y

Universe == {Elem1, Elem2, Elem3}

Init ==
    /\ X \in SUBSET({Elem1, Elem2})
    /\ Y = Universe

Next ==
    /\ Y' = Y
    /\ X' \subseteq Y

TypeOK ==
    /\ X \in SUBSET(Universe)
    /\ Y = Universe

EnabledSingleton ==
    ENABLED(\lambda X', Y': X' \subseteq {Elem1})

Inv ==
    /\ X \subseteq Universe
    /\ EnabledSingleton

FullSetCount == \_POSSIBLE( X' = Universe )
NewElementCount == \_POSSIBLE( (X' = X \/ {Elem3}) /\ Elem3 \notin X )

Post ==
    /\ FullSetCount = 1
    /\ NewElementCount = IF Elem3 \notin X THEN 1 ELSE 0

Spec == Init /\ [][Next]_<<X,Y>> /\ TypeOK /\ Inv

=============================================================================