------------------------------ MODULE ConstantZero ------------------------------

EXTENDS Integers

CONSTANTS Zero

ASSUME Zero = 0

VARIABLE x

Init == x = Zero

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

InitProp == x = 0

SafetyInvariant == x = 0

LivenessProp == <>[] (x = 0)

=============================================================================