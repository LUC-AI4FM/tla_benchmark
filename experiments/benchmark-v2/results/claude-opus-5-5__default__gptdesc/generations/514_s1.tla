------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract (high-level) specification of the Alternating Bit protocol.    *)
(* It describes what the protocol is supposed to accomplish: process A     *)
(* repeatedly chooses a new data value and passes it to process B, with a  *)
(* bit that alternates between 0 and 1.  Message transmission details     *)
(* are not modeled.                                                        *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data   \* The set of payload values that can be sent.

VARIABLES AVar,  \* The last message chosen by process A.
          BVar   \* The last message received by process B.

vars == << AVar, BVar >>

\* The set of all messages: records with a data field and an alternating bit.
Msgs == [data : Data, bit : {0, 1}]

\* Type-correctness invariant.
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs

\* Initially A holds some message with bit 1, and B has already received it.
Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar

\* Process A: once B has received the current message, A chooses a new
\* data value and flips the bit.
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

\* Process B: receives the new message from A.
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

\* All behaviors start in Init and evolve by Next steps, with stuttering.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Additional safety invariant: B's bit either matches A's, or B is exactly
\* one message behind (its bit differs from A's).
Inv == /\ TypeOK
       /\ (AVar.bit = BVar.bit) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================