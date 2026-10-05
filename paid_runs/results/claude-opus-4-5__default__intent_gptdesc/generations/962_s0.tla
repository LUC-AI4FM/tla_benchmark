---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES
    senderBit,        \* Current sequence bit of sender (0 or 1)
    senderData,       \* Current data item sender is trying to send
    senderWaiting,    \* TRUE if sender is waiting for ACK, FALSE if ready for new data
    sentMessages,     \* Set of messages in transit from sender to receiver
    receiverBit,      \* Last accepted sequence bit by receiver (0 or 1)
    receiverDelivered,\* Sequence of delivered data items
    ackMessages,      \* Set of ACKs in transit from receiver to sender
    sentHistory       \* Sequence of data items sender has initiated sending

Bit == {0, 1}

Message == [data: Data, bit: Bit]

Ack == [bit: Bit]

TypeInvariant ==
    /\ senderBit \in Bit
    /\ senderData \in Data \cup {<<>>}
    /\ senderWaiting \in BOOLEAN
    /\ sentMessages \subseteq Message
    /\ receiverBit \in Bit
    /\ receiverDelivered \in Seq(Data)
    /\ ackMessages \subseteq Ack
    /\ sentHistory \in Seq(Data)

Init ==
    /\ senderBit = 0
    /\ senderData = <<>>
    /\ senderWaiting = FALSE
    /\ sentMessages = {}
    /\ receiverBit = 1
    /\ receiverDelivered = <<>>
    /\ ackMessages = {}
    /\ sentHistory = <<>>

SenderInitiate(d) ==
    /\ senderWaiting = FALSE
    /\ senderData' = d
    /\ senderWaiting' = TRUE
    /\ sentHistory' = Append(sentHistory, d)
    /\ UNCHANGED <<senderBit, sentMessages, receiverBit, receiverDelivered, ackMessages>>

SenderTransmit ==
    /\ senderWaiting = TRUE
    /\ senderData # <<>>
    /\ sentMessages' = sentMessages \cup {[data |-> senderData, bit |-> senderBit]}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, receiverBit, receiverDelivered, ackMessages, sentHistory>>

SenderReceiveAck ==
    /\ senderWaiting = TRUE
    /\ \E ack \in ackMessages:
        /\ ack.bit = senderBit
        /\ senderBit' = (senderBit + 1) % 2
        /\ senderWaiting' = FALSE
        /\ ackMessages' = ackMessages \ {ack}
    /\ UNCHANGED <<senderData, sentMessages, receiverBit, receiverDelivered, sentHistory>>

SenderIgnoreOldAck ==
    /\ \E ack \in ackMessages:
        /\ ack.bit # senderBit
        /\ ackMessages' = ackMessages \ {ack}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, sentHistory>>

ReceiverReceive ==
    /\ \E msg \in sentMessages:
        /\ msg.bit # receiverBit
        /\ receiverBit' = msg.bit
        /\ receiverDelivered' = Append(receiverDelivered, msg.data)
        /\ sentMessages' = sentMessages \ {msg}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, ackMessages, sentHistory>>

ReceiverIgnoreDuplicate ==
    /\ \E msg \in sentMessages:
        /\ msg.bit = receiverBit
        /\ sentMessages' = sentMessages \ {msg}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, receiverBit, receiverDelivered, ackMessages, sentHistory>>

ReceiverSendAck ==
    /\ ackMessages' = ackMessages \cup {[bit |-> receiverBit]}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, sentHistory>>

LoseMessage ==
    /\ sentMessages # {}
    /\ \E msg \in sentMessages:
        sentMessages' = sentMessages \ {msg}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, receiverBit, receiverDelivered, ackMessages, sentHistory>>

LoseAck ==
    /\ ackMessages # {}
    /\ \E ack \in ackMessages:
        ackMessages' = ackMessages \ {ack}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, sentHistory>>

DuplicateMessage ==
    /\ sentMessages # {}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>

DuplicateAck ==
    /\ ackMessages # {}
    /\ UNCHANGED <<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>

Next ==
    \/ \E d \in Data: SenderInitiate(d)
    \/ SenderTransmit
    \/ SenderReceiveAck
    \/ SenderIgnoreOldAck
    \/ ReceiverReceive
    \/ ReceiverIgnoreDuplicate
    \/ ReceiverSendAck
    \/ LoseMessage
    \/ LoseAck
    \/ DuplicateMessage
    \/ DuplicateAck

Fairness ==
    /\ SF_<<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>(SenderTransmit)
    /\ SF_<<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>(ReceiverSendAck)
    /\ SF_<<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>(ReceiverReceive)
    /\ SF_<<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>>(SenderReceiveAck)

Spec == Init /\ [][Next]_<<senderBit, senderData, senderWaiting, sentMessages, receiverBit, receiverDelivered, ackMessages, sentHistory>> /\ Fairness

DeliveredSubsetOfSent ==
    \A i \in 1..Len(receiverDelivered):
        \E j \in 1..Len(sentHistory):
            receiverDelivered[i] = sentHistory[j]

NoDuplicateDelivery ==
    \A i, j \in 1..Len(receiverDelivered):
        (i # j) => 
            \/ receiverDelivered[i] # receiverDelivered[j]
            \/ \E k1, k2 \in 1..Len(sentHistory):
                /\ k1 # k2
                /\ sentHistory[k1] = receiverDelivered[i]
                /\ sentHistory[k2] = receiverDelivered[j]

DeliveryMatchesSendOrder ==
    Len(receiverDelivered) <= Len(sentHistory) /\
    \A i \in 1..Len(receiverDelivered):
        receiverDelivered[i] = sentHistory[i]

Safety ==
    /\ DeliveredSubsetOfSent
    /\ DeliveryMatchesSendOrder

AckBitConsistency ==
    \A ack \in ackMessages:
        ack.bit = receiverBit \/ ack.bit = (receiverBit + 1) % 2

BitAgreementInvariant ==
    (senderWaiting = FALSE) => 
        (senderBit = (receiverBit + 1) % 2)

NoDeadlock ==
    \/ senderWaiting = FALSE
    \/ sentMessages # {}
    \/ ackMessages # {}
    \/ ENABLED SenderTransmit
    \/ ENABLED ReceiverSendAck

EventualDelivery ==
    \A i \in 1..Len(sentHistory):
        <>(Len(receiverDelivered) >= i)

Progress ==
    [](senderWaiting => <>(~senderWaiting))

Liveness ==
    /\ Progress
    /\ EventualDelivery

=============================================================================