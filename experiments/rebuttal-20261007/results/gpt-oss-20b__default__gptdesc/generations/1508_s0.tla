------------------------------ MODULE SmallSM ------------------------------
VARIABLE x

MyNat == 0 .. 30
TypeOK == x \in MyNat

Init == x = 0

A ==
  /\ x' = x + 1
  /\ x < 30

BandC ==
  /\ x' = x - 1
  /\ x > 0

DandE ==
  /\ x' = x

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [] [Next]_x /\ []Inv

=============================================================================