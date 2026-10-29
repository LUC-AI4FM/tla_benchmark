------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract specification of what the Alternating Bit protocol is meant  *)
(* to accomplish.  There are three processes:                             *)
(*   A : takes the next pending data value from NewValQueue and makes it  *)
(*       the current sent message, flipping the alternating bit.          *)
(*   B : copies A's value when the alternating bit has changed.           *)
(*   E : the environment, which nondeterministically appends new data     *)
(*       values from Data to NewValQueue.                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,        \* <<value, bit>> currently being sent by A
          BVar,        \* <<value, bit>> last received by B
          NewValQueue  \* queue of pending data values to be sent

vars == << AVar, BVar, NewValQueue >>

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ UNCHANGED BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

E == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

-----------------------------------------------------------------------------
(* Safety: if the bits agree, then B holds exactly A's current message.   *)
Inv == /\ TypeOK
       /\ (AVar[2] = BVar[2]) => (AVar = BVar)

(* Liveness: every message sent by A is eventually received by B.         *)
Liveness == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Liveness
=============================================================================