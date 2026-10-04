---------------------------- MODULE NondetPositive ----------------------------

EXTENDS Integers

CONSTANTS InitialValue, AllowedValues

ASSUME InitialValue \in Int
ASSUME AllowedValues \subseteq Int
ASSUME InitialValue \in AllowedValues
ASSUME \A v \in AllowedValues : v > 0

VARIABLES x

TypeOK == x \in Int

Init == x = InitialValue

Next == \E v \in AllowedValues : v > 0 /\ x' = v

Spec == Init /\ [][Next]_x

SafetyInvariant == x # 0

PositiveInvariant == x > 0

ValueInAllowedSet == x \in AllowedValues

TransitionRespectConstraint == [][(\E v \in AllowedValues : v > 0 /\ x' = v) \/ UNCHANGED x]_x

=============================================================================