------------------------------- MODULE AlternatingBit -------------------------------

EXTENDS Naturals

CONSTANT Data

ASSUME Data # {}

VARIABLES sbit, rbit, ack, sndVal, rcvVal

vars == << sbit, rbit, ack, sndVal, rcvVal >>

DInit == CHOOSE d \in Data : TRUE

TypeOK ==
  /\ sbit \in {0, 1}
  /\ rbit \in {0, 1}
  /\ ack \in {0, 1}
  /\ sndVal \in Data
  /\ rcvVal \in Data

Init ==
  /\ sbit = 0
  /\ rbit = 0
  /\ ack = 0
  /\ sndVal = DInit
  /\ rcvVal = DInit

SendNew ==
  /\ ack = sbit
  /\ sbit' = 1 - sbit
  /\ sndVal' \in Data
  /\ UNCHANGED << rbit, rcvVal, ack >>

ReceiveMsg ==
  /\ rbit # sbit
  /\ rbit' = sbit
  /\ rcvVal' = sndVal
  /\ UNCHANGED << sbit, sndVal, ack >>

ReceiveAck ==
  /\ rbit # ack
  /\ ack' = rbit
  /\ UNCHANGED << sbit, rbit, sndVal, rcvVal >>

Next == SendNew \/ ReceiveMsg \/ ReceiveAck

Safety == []TypeOK

OutOfSync == sbit # ack
InfOftenOutOfSync == []<>OutOfSync

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveMsg)
  /\ WF_vars(ReceiveAck)
  /\ Safety
  /\ InfOftenOutOfSync

=============================================================================