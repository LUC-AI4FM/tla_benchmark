------------------------------- MODULE SingleVarNondet -------------------------------
EXTENDS Integers, TLC

CONSTANTS
    InitInt,    \* A concrete initial integer value (to be set in the model)
    Allowed     \* A small finite set of integers from which updates may nondeterministically choose

ASSUME
    /\ InitInt \in Int
    /\ Allowed \subseteq Int
    /\ IsFiniteSet(Allowed)

VARIABLES v

Init ==
    v = InitInt

Update ==
    /\ v' \in Allowed
    /\ v' > 0

Next ==
    Update

Spec ==
    Init /\ [][Next]_v

(*
 Safety invariant: the state variable is never equal to zero at any reachable state.
 To be checked against Spec (e.g., as a TLC invariant).
*)
NeverZero ==
    v # 0

(*
 Temporal transition constraint: every step either stutters or assigns a value
 from the permitted finite set and the value is strictly positive.
 This property is ensured by Spec and can also be checked explicitly.
*)
AllowedTransitionConstraint ==
    [] [Update]_v
=============================================================================