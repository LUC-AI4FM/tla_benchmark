---------------------------- MODULE Specification ----------------------------

EXTENDS Integers

CONSTANTS AllowedValues, InitialValue

VARIABLES x

TypeOK == x \in Int

Init == x = InitialValue

Next == \E v \in AllowedValues : v > 0 /\ x' = v

Spec == Init /\ [][Next]_x

SafetyInvariant == x /= 0

TransitionConstraint == [][(\E v \in AllowedValues : v > 0 /\ x' = v) \/ UNCHANGED x]_x

=============================================================================