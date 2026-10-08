MODULE SimpleInvariantDemo
EXTENDS Naturals

VARIABLE x

Init == x = 0

SetFixedConstant == x' = 5

AssignBoundedRange == \E y \in {1,2,3} : x' = y

SetOutOfRange == x' = 10

Mapping01 == (x = 0 /\ x' = 1)

Mapping10 == (x = 1 /\ x' = 0)

NonStutterStep == SetFixedConstant \/ AssignBoundedRange \/ SetOutOfRange \/ Mapping01 \/ Mapping10

Stutter == x' = x

NextClosed == NonStutterStep \/ Stutter

Invariant == (x \in {0,1,2,3}) /\ (x = 0)

Spec == Init /\ [][NextClosed]_x /\ []Invariant
