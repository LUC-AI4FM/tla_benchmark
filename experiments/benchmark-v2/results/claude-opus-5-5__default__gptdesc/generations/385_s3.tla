---------------------------- MODULE TheoremRefs ----------------------------
EXTENDS Naturals

CONSTANT C

VARIABLE x

vars == <<x>>

ASSUME AssumeCNat == C \in Nat

ASSUME AssumeCPos == C >= 1

N == INSTANCE Naturals

Init == x = 0

Inc ==
    /\ x < C
    /\ x' = x + 1

Reset ==
    /\ x = C
    /\ x' = 0

Next ==
    \/ Inc
    \/ Reset

Spec ==
    /\ Init
    /\ [][Next]_x
    /\ WF_x(Next)

TypeOK == x \in N!Nat /\ x \in 0..C

Bounded == x <= C

InitPart  == Spec!1
BoxPart   == Spec!2
FairPart  == Spec!3

IncGuard  == Inc!1
IncEffect == Inc!2
ResetGuard == Reset!1

FirstAction  == Next!1
SecondAction == Next!2

NatRef == N!Nat

PlusRef(a, b) == N!+(a, b)

SafetySpec == InitPart /\ BoxPart

LiveReset == []<>(x = 0)

LiveMax == []<>(x = C)

THEOREM InitTypeOK == Init => TypeOK

THEOREM SpecTypeOK == Spec => []TypeOK

THEOREM SpecBounded == Spec => []Bounded

THEOREM SafetyTypeOK == SafetySpec => []TypeOK

THEOREM SpecLiveReset == Spec => LiveReset

THEOREM SpecLiveMax == Spec => LiveMax

THEOREM AssumeRef == C \in NatRef

=============================================================================