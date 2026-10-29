------------------------------ MODULE ABSpec ------------------------------
EXTENDS Integers

CONSTANT Data  \* The set of all possible data values.

VARIABLES AVar,   \* The last <<value, bit>> pair A decided to send.
          BVar    \* The last <<value, bit>> pair B received.

vars == << AVar, BVar >>

(***************************************************************************)
(* Messages are records with a data field and a single bit (0 or 1).      *)
(***************************************************************************)
TypeOK == /\ AVar \in [data : Data, bit : {0, 1}]
          /\ BVar \in [data : Data, bit : {0, 1}]

(***************************************************************************)
(* Initially both variables are equal, with the bit set to 1.             *)
(***************************************************************************)
Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar

(***************************************************************************)
(* A: when the bits of AVar and BVar match, the sender chooses any data   *)
(* value from Data, updating AVar with it and flipping the bit.           *)
(***************************************************************************)
A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data :
          AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ UNCHANGED BVar

(***************************************************************************)
(* B: when the bits differ, the receiver copies AVar to BVar,             *)
(* acknowledging receipt.                                                  *)
(***************************************************************************)
B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars
=============================================================================