---- MODULE DigitParity ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

TypeOK == x \in 0..9

Even == x % 2 = 0

Safe == x \in 0..9 /\ x % 2 = 0

Init == x = 0

Next == x' \in {v \in 0..9 : v % 2 = 0}

Spec == Init /\ [][Next]_vars

SafetyInv == Safe

AlwaysSafe == []Safe

StepClosure == [][Safe => Safe']_vars

StutterPreserves == [][(UNCHANGED x /\ Safe) => Safe']_vars

THEOREM InitSafe == Init => Safe
THEOREM SafeInductive == Safe /\ [Next]_vars => Safe'
THEOREM Spec => []Safe
====