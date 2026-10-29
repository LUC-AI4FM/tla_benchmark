---- MODULE Countdown ----
EXTENDS Naturals, Integers

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLE x

vars == <<x>>

TypeOK == x \in Int

Init == x = N

Decrement == /\ x > 0
             /\ x' = x - 1

StayAtZero == /\ x = 0
              /\ x' = x

Next == Decrement \/ StayAtZero

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

NonNegative == x >= 0

Invariant == TypeOK /\ NonNegative

ProgressEnabled == (x > 0) => ENABLED Decrement

AlwaysProgressEnabled == [](ProgressEnabled)

Progress == \A k \in 0..N : (x = k /\ k > 0) ~> (x < k)

EventuallyZero == <>(x = 0)

Termination == (N > 0) => <>(x = 0)

StaysZero == <>[](x = 0)

StableAtZero == [](x = 0 => [](x = 0))

====