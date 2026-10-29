------------------------------ MODULE ABSpec ------------------------------
(***************************************************************************)
(* Abstract behavioral specification of the Alternating Bit protocol.      *)
(* Process A chooses new data and flips the bit when the bits of AVar and  *)
(* BVar match.  Process B copies A's value when the bits differ.           *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data

VARIABLES AVar, BVar

vars == << AVar, BVar >>

Msgs == [val : Data, bit : {0, 1}]

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs

Init == /\ AVar \in [val : Data, bit : {1}]
        /\ BVar = AVar

(* Process A: when the bits agree, choose new data and flip the bit. *)
A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data : AVar' = [val |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

(* Process B: when the bits differ, copy A's value. *)
B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

-----------------------------------------------------------------------------
(* Safety: whenever the bits agree, B holds exactly A's message. *)
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

(* Liveness: every message chosen by A is eventually received by B. *)
Liveness == \A d \in Data, b \in {0, 1} :
              (AVar = [val |-> d, bit |-> b]) ~> (BVar = [val |-> d, bit |-> b])

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Liveness
=============================================================================