------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* An abstract behavioral specification of the Alternating Bit protocol.  *)
(* It describes what the protocol is intended to accomplish, not how      *)
(* messages are transmitted. Process A decides to send a new data value   *)
(* with an alternated bit. Process B receives the value A last decided    *)
(* to send.                                                               *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data            \* The set of all possible payload values.

VARIABLES AVar,          \* The last [data, bit] message A decided to send.
          BVar           \* The last [data, bit] message B received.

vars == << AVar, BVar >>

Msg == [data : Data, bit : {0, 1}]

TypeOK == /\ AVar \in Msg
          /\ BVar \in Msg

---------------------------------------------------------------------------
Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar

(***************************************************************************)
(* A: once B has received the last message, A chooses a new data value   *)
(* and flips the bit.                                                     *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

(***************************************************************************)
(* B: receives the message that A last decided to send.                   *)
(***************************************************************************)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety: B's received message is either A's current message or the     *)
(* previous one (bits differ in that case).                               *)
(***************************************************************************)
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================