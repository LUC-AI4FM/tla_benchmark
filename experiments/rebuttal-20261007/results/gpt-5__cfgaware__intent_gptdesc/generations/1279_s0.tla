------------------------------ MODULE SingleVarNondet ------------------------------

EXTENDS Integers

CONSTANTS InitVal, AllowedVals

VARIABLE x

ASSUME /\ InitVal \in Int
       /\ AllowedVals \subseteq Int

Allowed(v) == v \in AllowedVals /\ v > 0

Init == x = InitVal

Next == Allowed(x')

Spec == Init /\ [][Next]_x

Invariant == x /= 0
Inv == Invariant
SafetyInvariant == Invariant

TransitionOK == [](x' = x \/ Allowed(x'))
AllowedTransition == TransitionOK
TransitionConstraint == TransitionOK

=============================================================================