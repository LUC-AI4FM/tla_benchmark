------------------------------ MODULE ABP ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES sData, rData, sendBit, ackBit, recvBit

vars == <<sData, rData, sendBit, ackBit, recvBit>>

Init ==
  /\ sData ∈ Data
  /\ rData ∈ Data
  /\ sendBit = 0
  /\ ackBit = 0
  /\ recvBit = 0

SendAction ==
  /\ ackBit = sendBit
  /\ sData' ∈ Data
  /\ sendBit' = 1 - sendBit
  /\ rData' = rData
  /\ ackBit' = ackBit
  /\ recvBit' = recvBit

ReceiveAction ==
  /\ recvBit # sendBit
  /\ rData' = sData
  /\ recvBit' = sendBit
  /\ sData' = sData
  /\ ackBit' = ackBit
  /\ sendBit' = sendBit

AckAction ==
  /\ ackBit # recvBit
  /\ ackBit' = recvBit
  /\ sData' = sData
  /\ rData' = rData
  /\ sendBit' = sendBit
  /\ recvBit' = recvBit

Stutter ==
  /\ sData' = sData
  /\ rData' = rData
  /\ sendBit' = sendBit
  /\ ackBit' = ackBit
  /\ recvBit' = recvBit

Next == SendAction \/ ReceiveAction \/ AckAction \/ Stutter

BitsInvariants ==
  /\ sendBit ∈ {0,1}
  /\ ackBit ∈ {0,1}
  /\ recvBit ∈ {0,1}

DataInvariants ==
  /\ sData ∈ Data
  /\ rData ∈ Data

TypeInv == BitsInvariants /\ DataInvariants

WF_Receive == WF_vars(ReceiveAction)
WF_Ack == WF_vars(AckAction)

Spec == Init /\ [][Next]_vars /\ WF_Receive /\ WF_Ack /\ []TypeInv

============================================================================