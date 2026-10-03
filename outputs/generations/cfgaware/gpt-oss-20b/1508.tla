------------------------------ MODULE SmallSM ------------------------------
EXTENDS Naturals

CONSTANT MyNat
VARIABLE x

(* The configuration must set MyNat == 0..30 *)

TypeOK == x \in MyNat

Init == x = 0

A     == /\ x' = x + 1
BandC == /\ x' = x - 1
DandE == /\ x' = x * 2

Next == A \/ BandC \/ DandE

Inv   == TypeOK

Spec  == Init /\ [] Inv /\ [] [Next]_x

=============================================================================