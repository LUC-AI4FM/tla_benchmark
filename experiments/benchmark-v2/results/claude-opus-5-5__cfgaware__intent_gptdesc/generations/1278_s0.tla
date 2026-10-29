---- MODULE DigitParity ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

Safe(v) == v \in 0..9 /\ v % 2 = 0

TypeOK == x \in 0..9

EvenInv == x % 2 = 0

Inv == TypeOK /\ EvenInv

Init == x = 0

Next == \E v \in 0..9 : Safe(v) /\ x' = v

Spec == Init /\ [][Next]_vars

SafetyProperty == []Inv

THEOREM Spec => []Inv
====