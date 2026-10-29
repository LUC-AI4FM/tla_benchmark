------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract specification of what the Alternating Bit protocol is meant   *)
(* to accomplish.  Process A takes the next value from the queue of       *)
(* pending data values NewValQueue and makes it the current message,      *)
(* flipping the alternating bit.  Process B copies A's value when the     *)
(* alternating bit changes.  Process E (the environment)                  *)
(* nondeterministically appends new values from Data to the queue.        *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

(***************************************************************************)
(* A: when B has received the current message, take the next pending     *)
(* value from the queue and send it with the alternating bit flipped.     *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ UNCHANGED BVar

(***************************************************************************)
(* B: when the alternating bit changes, copy A's value.                   *)
(***************************************************************************)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

(***************************************************************************)
(* E: the environment appends a new data value to the queue.              *)
(***************************************************************************)
E == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: A and B agree on the value whenever their bits agree, and the  *)
(* bits differ only when A has sent a new value that B has not yet copied. *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) <=> (AVar = BVar)

(***************************************************************************)
(* Liveness: every value sent by A is eventually received by B, and every *)
(* pending value is eventually taken from the queue by A.                 *)
(***************************************************************************)
Delivery == (AVar # BVar) ~> (AVar = BVar)

QueueProgress == \A n \in Nat :
                    (Len(NewValQueue) > 0 /\ AVar = BVar)
                       ~> (AVar # BVar)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Delivery
=============================================================================