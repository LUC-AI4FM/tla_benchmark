MODULE H
VARIABLES x

MyNat == 0..30

Inv == x \in MyNat /\ x = 0

A == x' = 23

BandC == (x \in MyNat /\ x' \in 23..25) \/ (x < 25 /\ x' = 26)

DandE == (x = 23 /\ x' = 42) \/ (x = 123 /\ x' = 4711)

Next == A \/ BandC \/ DandE

Init == Inv

Spec == Init /\ [] [Next]_x