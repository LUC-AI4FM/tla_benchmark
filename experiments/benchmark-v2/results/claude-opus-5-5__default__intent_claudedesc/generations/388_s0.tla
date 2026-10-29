---- MODULE ModularCounter ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N = 6

VARIABLE x

vars == << x >>

TypeOK == x \in 0..(N - 1)

Init == x = 0

Increment == x' = (x + 1) % N

Next == Increment

Spec == Init /\ [][Next]_vars

\* Correctness property: the counter is always a natural number
IsNat == x \in Nat

NatInvariant == []IsNat

\* Demonstration that basic arithmetic facts are expressible and checkable
ArithmeticFact == 2 + 2 = 4

ASSUME ArithmeticAssumption == ArithmeticFact

THEOREM AdditionTheorem == 2 + 2 = 4

THEOREM SpecIsNat == Spec => NatInvariant

THEOREM SpecTypeOK == Spec => []TypeOK

====