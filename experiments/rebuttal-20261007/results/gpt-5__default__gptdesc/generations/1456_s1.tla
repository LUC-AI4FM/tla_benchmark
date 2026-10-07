------------------------------ MODULE TinyXY ------------------------------

EXTENDS Naturals, TLC

CONSTANTS S

ASSUME S = {1, 2, 3}

VARIABLES x, y

vars == << x, y >>

Init ==
    /\ y \in SUBSET S
    /\ x \in SUBSET y

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

\* State (safety) predicates
TypeInv == /\ x \in SUBSET S /\ y \in SUBSET S
SubsetInv == x \subseteq y

\* Named predicates for TLC coverage
FullSet == x = S
GainThree == /\ ~(3 \in x) /\ (3 \in x')

\* Coverage assertions using TLCGet over named predicates
Coverage ==
    /\ Assert(TLCGet("numOf", "FullSet") = 1, "Unexpected count for FullSet")
    /\ Assert(TLCGet("numOf", "GainThree") = 25, "Unexpected count for GainThree")

\* No full temporal spec operator and no fairness condition
Spec == Init /\ Next

============================================================================