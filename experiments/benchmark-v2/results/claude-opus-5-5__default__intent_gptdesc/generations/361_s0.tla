---- MODULE ThreeRangeStable ----
EXTENDS Integers, FiniteSets

CONSTANTS XMax, YMax, ZMax

ASSUME XMax = 100 /\ YMax = 200 /\ ZMax = 20

VARIABLES x, y, z

vars == <<x, y, z>>

XRange == 1..XMax
YRange == 1..YMax
ZRange == 1..ZMax

\* Full initial-state space: Cartesian product of the three ranges
InitStates == XRange \X YRange \X ZRange

\* Number of initial states = |1..100| * |1..200| * |1..20| = 400000
NumInitStates == Cardinality(XRange) * Cardinality(YRange) * Cardinality(ZRange)

ASSUME NumInitStates = XMax * YMax * ZMax

TypeOK ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

Init ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

\* Identity transition relation: no component changes
Next ==
    /\ x' = x
    /\ y' = y
    /\ z' = z

\* A valid execution begins with a triple from the allowed ranges
\* and then never modifies any component.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: each component stays within its original bounds
XInBounds == x >= 1 /\ x <= XMax
YInBounds == y >= 1 /\ y <= YMax
ZInBounds == z >= 1 /\ z <= ZMax

StateInInitSpace == <<x, y, z>> \in InitStates

SafetyInv == XInBounds /\ YInBounds /\ ZInBounds /\ TypeOK

\* Determinism after initialization: every step is the identity
NoChange == [][UNCHANGED vars]_vars

\* Liveness / stability: eventually the state never changes again
\* (holds from the very first state)
Stability == \A a \in XRange, b \in YRange, c \in ZRange :
                 (<<x, y, z>> = <<a, b, c>>) => [](<<x, y, z>> = <<a, b, c>>)

EventuallyStable == <>[][UNCHANGED vars]_vars

THEOREM Spec => []SafetyInv
THEOREM Spec => []StateInInitSpace
THEOREM Spec => NoChange
THEOREM Spec => Stability
====