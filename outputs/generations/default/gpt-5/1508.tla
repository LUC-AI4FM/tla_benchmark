------------------------------ MODULE SmallXMachine ------------------------------

EXTENDS Naturals, Integers

VARIABLES x

MyNat == 0..30

TypeOK == x \in MyNat

Inv == TypeOK

Init == x = 0

Even(n) == ∃ k \in Nat : n = 2 * k

A ==
  /\ x < 30
  /\ x' = x + 1

BandC ==
  \/ /\ x > 0
     /\ x' = x - 1
  \/ /\ x >= 2
     /\ Even(x)
     /\ x' = x \div 2

DandE ==
  \/ /\ x <= 28
     /\ x' = x + 2
  \/ /\ x >= 1
     /\ x' = x - 1

Next == A \/ BandC \/ DandE

Spec == Init /\ [][Next]_x /\ []Inv

=============================================================================