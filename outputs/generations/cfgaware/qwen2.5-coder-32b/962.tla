---------------------------- MODULE ABCSpec ----------------------------

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sentData, receivedData

(*--algorithm AlternatingBitProtocol
variables sendBit \in {0, 1} = 0,
          ackBit \in {0, 1} = 0,
          recvBit \in {0, 1} = 0,
          sentData \in DataValues,
          receivedData \in DataValues;

begin

Init ==
    /\ sendBit = 0
    /\ ackBit = 0
    /\ recvBit = 0

Next ==
    \/ /\ sendBit = ackBit
       /\ UNCHANGED <<recvBit, receivedData>>
       /\ sentData' \in DataValues
       /\ sendBit' = 1 - sendBit
       /\ ackBit' = ackBit
    \/ /\ recvBit # sendBit
       /\ sentData' = sentData
       /\ sendBit' = sendBit
       /\ ackBit' = ackBit
       /\ receivedData' \in DataValues
       /\ recvBit' = 1 - recvBit
    \/ /\ recvBit # ackBit
       /\ sentData' = sentData
       /\ sendBit' = sendBit
       /\ ackBit' = 1 - ackBit
       /\ receivedData' = receivedData
       /\ recvBit' = recvBit

TypeInv ==
    /\ sendBit \in {0, 1}
    /\ ackBit \in {0, 1}
    /\ recvBit \in {0, 1}
    /\ sentData \in DataValues
    /\ receivedData \in DataValues

Spec ==
    Init /\ [][Next]_<<sendBit, ackBit, recvBit, sentData, receivedData>>

WF_Send ==
    WF_next(<<sendBit, ackBit, recvBit, sentData, receivedData>>, Next)

WF_Ack ==
    WF_next(<<sendBit, ackBit, recvBit, sentData, receivedData>>, Next)

Inv ==
    TypeInv

THEOREM Spec => <>[](sendBit # ackBit)

end algorithm *)
=============================================================================