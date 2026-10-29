---- MODULE ConstantSum ----
EXTENDS Naturals

CONSTANTS A, B, MaxInt

ASSUME WellFormed ==
    /\ A \in Nat
    /\ B \in Nat
    /\ MaxInt \in Nat
    /\ A + B <= MaxInt

VARIABLES a, b, sum

vars == <<a, b, sum>>

TypeOK ==
    /\ a \in Nat
    /\ b \in Nat
    /\ sum \in 0..MaxInt

Init ==
    /\ a = A
    /\ b = B
    /\ sum = A + B

Stutter ==
    /\ UNCHANGED vars

Next == Stutter

Spec == Init /\ [][Next]_vars

SumCorrect == sum = a + b

SumNonNegative == sum >= 0

NoOverflow == sum <= MaxInt

InputsConstant == a = A /\ b = B

AlwaysSumCorrect == [](sum = a + b)

InputsNeverChange == [][a' = a /\ b' = b]_vars

SumNeverChanges == [][sum' = sum]_vars

SumAlwaysConstant == [](sum = A + B)

THEOREM Spec => [](TypeOK /\ SumCorrect /\ SumNonNegative /\ NoOverflow /\ InputsConstant)
THEOREM Spec => AlwaysSumCorrect
THEOREM Spec => InputsNeverChange /\ SumNeverChanges /\ SumAlwaysConstant
====