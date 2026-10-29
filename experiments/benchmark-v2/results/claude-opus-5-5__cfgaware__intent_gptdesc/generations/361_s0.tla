---------------------------- MODULE StableTriple ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y, z

vars == <<x, y, z>>

RangeX == 1..100
RangeY == 1..200
RangeZ == 1..20

\* Number of initial states = |RangeX| * |RangeY| * |RangeZ| = 100 * 200 * 20
NumInitStates == Cardinality(RangeX) * Cardinality(RangeY) * Cardinality(RangeZ)

TypeOK == /\ x \in RangeX
          /\ y \in RangeY
          /\ z \in RangeZ

Init == /\ x \in RangeX
        /\ y \in RangeY
        /\ z \in RangeZ

\* The transition relation is the identity: nothing ever changes.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safety properties: each component stays within its original bounds.
XInBounds == x \in RangeX
YInBounds == y \in RangeY
ZInBounds == z \in RangeZ

Inv == XInBounds /\ YInBounds /\ ZInBounds

\* Stability: every step leaves the state unchanged.
Stable == [][UNCHANGED vars]_vars

\* Liveness-style stability: eventually (indeed always) no further change occurs.
NoFurtherChange == \A a \in RangeX, b \in RangeY, c \in RangeZ :
                     (x = a /\ y = b /\ z = c) => [](x = a /\ y = b /\ z = c)

StabilityLiveness == <>[](UNCHANGED vars)

THEOREM Spec => []Inv
THEOREM Spec => Stable
=============================================================================