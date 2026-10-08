------------------------------ MODULE ABP ------------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES sData, rData, sendBit, recvBit, ackBit

vars == <<sData, rData, sendBit, recvBit, ackBit>>

TypeInv ==
  /\ sData ∈ Data
  /\ rData ∈ Data
  /\ sendBit ∈ {0,1}
  /\ recvBit ∈ {0,1}
  /\ ackBit ∈ {0,1}

Init ==
  /\ sData ∈ Data
  /\ rData ∈ Data
  /\ sendBit = 0
  /\ recvBit = 0
  /\ ackBit = 0

SendAction ==
  /\ ackBit = sendBit
  /\ sData' ∈ Data
  /\ sendBit' = 1 - sendBit
  /\ UNCHANGED <<rData, recvBit, ackBit>>

ReceiveAction ==
  /\ recvBit #= sendBit
  /\ rData' = sData
  /\ recvBit' = sendBit
  /\ UNCHANGED <<sData, sendBit, ackBit>>

AckAction ==
  /\ ackBit #= recvBit
  /\ ackBit' = recvBit
  /\ UNCHANGED <<sData, rData, sendBit, recvBit>>

Stutter ==
  UNCHANGED vars

Next == SendAction \/ ReceiveAction \/ AckAction \/ Stutter

ABCSpec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveAction)
  /\ WF_vars(AckAction)
  /\ []TypeInv

=============================================================================