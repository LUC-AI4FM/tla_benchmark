---------------------------- MODULE ParamInstance ----------------------------
EXTENDS Naturals

CONSTANT Bound

ASSUME BoundAssumption == Bound \in Nat

----------------------------- MODULE Counter ---------------------------------
VARIABLE x

CInit == x = 0

CNext == x' = (x + 1) % (Bound + 1)

CSpec == CInit /\ [][CNext]_x

CTypeOK == x \in 0..Bound
==============================================================================