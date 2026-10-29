---------------------------- MODULE Countdown ----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------

Init == x = N

Decrement ==
    /\ x > 0
    /\ x' = x - 1

StayAtZero ==
    /\ x = 0
    /\ x' = x

Next == Decrement \/ StayAtZero

Spec == Init /\ [][Next]_vars /\ WF_vars(Decrement)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK == x \in Int

NatType == x \in Nat

NonNegative == x >= 0

Bounded == x \in 0..N

\* Whenever the value is positive, a decrementing step is enabled
ProgressEnabled == [](x > 0 => ENABLED Decrement)

\* Once zero, the value stays zero forever
ZeroIsStable == [](x = 0 => [](x = 0))

\* Every step either decrements by exactly one or keeps zero unchanged
StepShape == [][(x > 0 /\ x' = x - 1) \/ (x = 0 /\ x' = 0)]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* From any positive value, the system eventually reaches a strictly smaller value
Progress == \A k \in 0..N : (x = k /\ k > 0) ~> (x < k)

\* From any positive value, the system eventually reaches zero
PositiveLeadsToZero == (x > 0) ~> (x = 0)

\* The system eventually terminates at zero
EventuallyZero == <>(x = 0)

\* The system eventually stutters at zero forever
EventuallyAlwaysZero == <>[](x = 0)

-----------------------------------------------------------------------------
\* Theorems

THEOREM Spec => []TypeOK
THEOREM Spec => []NatType
THEOREM Spec => []NonNegative
THEOREM Spec => []Bounded
THEOREM Spec => ProgressEnabled
THEOREM Spec => ZeroIsStable
THEOREM Spec => StepShape
THEOREM Spec => Progress
THEOREM Spec => PositiveLeadsToZero
THEOREM Spec => EventuallyZero
THEOREM Spec => EventuallyAlwaysZero

=============================================================================