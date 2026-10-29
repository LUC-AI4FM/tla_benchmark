------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Msgs == [data : Data, bit : {0, 1}]

VARIABLES AVar, BVar, NewValQueue

vars == <<AVar, BVar, NewValQueue>>

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Msgs
        /\ BVar = AVar
        /\ NewValQueue = << >>

(***************************************************************************)
(* Process E: the environment enqueues a new data value whenever the       *)
(* sender and receiver are synchronized (their bits match).                *)
(***************************************************************************)
E == /\ AVar.bit = BVar.bit
     /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED <<AVar, BVar>>

(***************************************************************************)
(* Process A: the sender dequeues a value when one is available, builds a  *)
(* new message with that data and the toggled bit, and updates AVar.       *)
(***************************************************************************)
A == /\ NewValQueue # << >>
     /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
     /\ NewValQueue' = Tail(NewValQueue)
     /\ UNCHANGED BVar

(***************************************************************************)
(* Process B: the receiver waits until the sender's bit differs from its   *)
(* own, then copies the sender's message, achieving synchronization.       *)
(***************************************************************************)
B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ UNCHANGED <<AVar, NewValQueue>>

Next == A \/ B \/ E

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

=============================================================================