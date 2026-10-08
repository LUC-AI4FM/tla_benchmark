---------------------------- MODULE spec ----------------------------

EXTENDS Naturals

CONSTANTS MinVal, MaxVal, InitVal

ASSUME MinVal \in Nat
ASSUME MaxVal \in Nat
ASSUME MinVal <= MaxVal
ASSUME InitVal \in Nat
ASSUME InitVal >= MinVal /\ InitVal <= MaxVal

VARIABLES x

TypeOK == x \in MinVal..MaxVal

Init == x = InitVal

UnconditionalAssignToMin == x' = MinVal

UnconditionalAssignToMax == x' = MaxVal

AssignToContiguousSubrange == 
    \E v \in (MinVal + 1)..(MaxVal - 1) : x' = v

GuardedIncrementFromInit ==
    /\ x = InitVal
    /\ x' = x + 1

GuardedDecrementFromMax ==
    /\ x = MaxVal
    /\ x' = x - 1

GuardedJumpFromMin ==
    /\ x = MinVal
    /\ x' = MaxVal

TransitionExceedingBound ==
    x' = MaxVal + 1

TransitionBelowBound ==
    x' = MinVal - 1

Next ==
    \/ UnconditionalAssignToMin
    \/ UnconditionalAssignToMax
    \/ AssignToContiguousSubrange
    \/ GuardedIncrementFromInit
    \/ GuardedDecrementFromMax
    \/ GuardedJumpFromMin
    \/ TransitionExceedingBound
    \/ TransitionBelowBound

Spec == Init /\ [][Next]_x

TypeInvariant == TypeOK

InitialValueInvariant == x = InitVal

SafetyInvariant == TypeOK /\ (x = InitVal)

=========================================================================