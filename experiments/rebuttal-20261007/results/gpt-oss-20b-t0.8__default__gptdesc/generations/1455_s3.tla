------------------- MODULE SubsetSpec -------------------
EXTENDS TLC, SETS

CONSTANTS INT, NAT

VARIABLE b

Init ==
    b = TRUE

SubsetExpr ==
    (1 .. 3) \subseteq {1,2,3,4} ∧
    {5,6} \subseteq INT ∧
    ~( {-1} \subseteq NAT ) ∧
    (INT \subseteq INT) ∧
    ({-10,-9} \subseteq INT) ∧
    ~(NAT \subseteq {0})

Next ==
    b' = SubsetExpr

TypeInv ==
    b \in BOOLEAN

Inv ==
    TypeInv /\ b = TRUE

Spec ==
    Init /\ [] Next

=======================================================