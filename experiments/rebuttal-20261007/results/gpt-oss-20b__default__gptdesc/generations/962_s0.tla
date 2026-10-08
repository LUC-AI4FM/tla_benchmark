------------------------------ MODULE AlternatingBitProtocol ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS DataSet, InitData

VARIABLES sendBit, recvBit, ackBit, sentData, receivedData

bitSet == {0, 1}

TypeInvariant ==
    /\ sendBit ∈ bitSet
    /\ recvBit ∈ bitSet
    /\ ackBit ∈ bitSet
    /\ sentData ∈ DataSet
    /\ receivedData ∈ DataSet
    /\ InitData ∈ DataSet

Init ==
    /\ sendBit = 0
    /\ recvBit = 1
    /\ ackBit = 1
    /\ sentData = InitData
    /\ receivedData = InitData

SenderSend ==
    /\ ackBit = sendBit
    /\ sentData' ∈ DataSet \ {sentData}
    /\ sendBit' = sendBit
    /\ recvBit' = recvBit
    /\ ackBit' = ackBit
    /\ receivedData' = receivedData

ReceiverAccept ==
    /\ recvBit #= sendBit
    /\ receivedData' = sentData
    /\ recvBit' = 1 - recvBit
    /\ sendBit' = sendBit
    /\ ackBit' = ackBit
    /\ sentData' = sentData

SenderAcceptAck ==
    /\ recvBit #= ackBit
    /\ sendBit' = 1 - sendBit
    /\ ackBit' = recvBit
    /\ recvBit' = recvBit
    /\ sentData' = sentData
    /\ receivedData' = receivedData

Next == SenderSend \/ ReceiverAccept \/ SenderAcceptAck

Spec ==
    Init
    /\ [][Next]_<<sendBit, recvBit, ackBit, sentData, receivedData>>
    /\ TypeInvariant
    /\ Fairness(ReceiverAccept)
    /\ Fairness(SenderAcceptAck)
    /\ □◇ (sendBit #= ackBit)

=============================================================================