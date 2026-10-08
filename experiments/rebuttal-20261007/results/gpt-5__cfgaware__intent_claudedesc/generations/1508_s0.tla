---- MODULE OneVarStutterDemo ----
EXTENDS Naturals

VARIABLES x

FixedConst == 5
BoundRange == 1..3
OutOfRangeVal == 7

SmallType == 0..2

Init == x = 0

Map1 == /\ x = 1
        /\ x' = 2

Map2 == /\ x = 2
        /\ x' = 1

Next ==
  \/ x' = FixedConst
  \/ x' \in BoundRange
  \/ x' = OutOfRangeVal
  \/ Map1
  \/ Map2

TypeOK == x \in Nat

Inv == /\ x \in SmallType
       /\ x = 0

Spec == /\ Init
        /\ []Inv
        /\ [][Next]_x

Correctness == /\ Init
               /\ Inv
               /\ [][Next]_x
====