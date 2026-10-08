------------------------------- MODULE AlternatingBitProtocol -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES sendBit, ackBit, recvBit, sendData, recvData

Init == /\ sendBit = 0 
        /\ ackBit = 0 
        /\ recvBit = 0 
        /\ sendData \in Data 
        /\ recvData \in Data

Next == \/ /\ sendBit = ackBit
             /\ \/ /\ sendData' \in Data
                    /\ sendBit' = 1 - sendBit
                    /\ UNCHANGED <<ackBit, recvBit, recvData>>
          \/ /\ sendBit # ackBit
             /\ ackBit' = recvBit
             /\ UNCHANGED <<sendBit, sendData, recvData>>
          \/ /\ recvBit # sendBit
             /\ recvData' = sendData
             /\ recvBit' = 1 - recvBit
             /\ UNCHANGED <<sendBit, ackBit>>

TypeInvariant == /\ sendBit \in {0, 1}
                 /\ ackBit \in {0, 1}
                 /\ recvBit \in {0, 1}
                 /\ sendData \in Data
                 /\ recvData \in Data

Spec == WF_next(Next) /\ SF_next(RecvAction \/ AckAction)

RecvAction == recvBit # sendBit

AckAction == sendBit # ackBit

=============================================================================