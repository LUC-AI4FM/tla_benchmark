---- MODULE SumSpec ----
EXTENDS Naturals, Integers

CONSTANTS Foo1, Foo2

VARIABLES Sum

vars == << Sum >>

\* Upper bound of the arithmetic domain assumed by the model
MaxValue == 2^31 - 1

ASSUME InputsAreNaturals == Foo1 \in Nat /\ Foo2 \in Nat
ASSUME NoOverflow == Foo1 + Foo2 \in 0..MaxValue

TypeOK == Sum \in Nat

Init == Sum = Foo1 + Foo2

\* The inputs are constants, so the sum never changes.
Next == UNCHANGED Sum

Spec == Init /\ [][Next]_vars

SumCorrect == Sum = Foo1 + Foo2

SumNonNegative == Sum >= 0

SumConstant == [][Sum' = Sum]_vars

AlwaysSumCorrect == [](Sum = Foo1 + Foo2)

THEOREM Spec => []TypeOK
THEOREM Spec => []SumCorrect
THEOREM Spec => []SumNonNegative
THEOREM Spec => AlwaysSumCorrect
====