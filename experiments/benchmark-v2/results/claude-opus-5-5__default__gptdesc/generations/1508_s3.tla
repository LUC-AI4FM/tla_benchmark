---------------------------- MODULE SmallStateMachine ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

-----------------------------------------------------------------------------
(* Next-state actions *)

A == /\ x < 30
     /\ x' = x + 1

B == /\ x + 2 <= 30
     /\ x' = x + 2

C == /\ x > 0
     /\ x' = x - 1

BandC == B \/ C

D == /\ x % 2 = 0
     /\ x > 0
     /\ x' = x \div 2

E == /\ x = 30
     /\ x' = 0

DandE == D \/ E

Next == A \/ BandC \/ DandE

-----------------------------------------------------------------------------
(* Invariant-like state predicate used as the initial predicate of Spec *)

Inv == Init /\ TypeOK

Spec == Inv /\ [][Next]_x

-----------------------------------------------------------------------------
(* Safety properties *)

TypeInvariant == TypeOK

THEOREM Spec => []TypeOK

=============================================================================