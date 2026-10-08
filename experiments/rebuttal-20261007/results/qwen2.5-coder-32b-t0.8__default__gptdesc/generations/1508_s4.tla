------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS MyNat

VARIABLES x

Init == x = 0

A   == /\ x \in MyNat 
     /\ x' = (x + 1) % 31

BandC == \/ /\ x \in MyNat
          /\ x' = (x - 1) % 31
         \/ /\ x \in MyNat
          /\ x' = (x + 2) % 31

DandE == \/ /\ x \in MyNat
          /\ x' = (x * 2) % 31
         \/ /\ x \in MyNat
          /\ x' = (x - 2) % 31

Next == A \/ BandC \/ DandE

TypeOK == x \in MyNat

Inv == TypeOK

Spec == Init /\ [][Next]_x /\ <>Invariant(Inv)

================================================================================