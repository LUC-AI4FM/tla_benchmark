------------------------------- MODULE AlternatingBitProtocol -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataItems \* The set of possible data items to be sent

VARIABLES 
    senderSeqBit, \* Sender's current sequence bit (0 or 1)
    receiverSeqBit, \* Receiver's last delivered sequence bit (0 or 1)
    channel, \* Messages in transit on the unreliable channel
    senderBuffer, \* The data item currently being sent by the sender
    receiverBuffer \* The data item currently being processed by the receiver

Init == 
    /\ senderSeqBit = 0
    /\ receiverSeqBit = 0
    /\ channel = {}
    /\ senderBuffer \in DataItems
    /\ receiverBuffer = <<>>

Next ==
    \/ \* Sender sends a new message if it has not yet received an acknowledgment for the previous one
       (/\ channel = {<<senderBuffer, senderSeqBit>>}
        /\ UNCHANGED receiverSeqBit
        /\ UNCHANGED receiverBuffer
        /\ senderBuffer' \in DataItems
        /\ senderSeqBit' = 1 - senderSeqBit)
    \/ \* Sender sends the initial message
       (/\ channel = {}
        /\ UNCHANGED receiverSeqBit
        /\ UNCHANGED receiverBuffer
        /\ senderBuffer' \in DataItems
        /\ senderSeqBit' = 0)
    \/ \* Message is lost in transit
       (/\ channel \in {<<senderBuffer, senderSeqBit>>}
        /\ channel' = {}
        /\ UNCHANGED senderSeqBit
        /\ UNCHANGED senderBuffer
        /\ UNCHANGED receiverSeqBit
        /\ UNCHANGED receiverBuffer)
    \/ \* Receiver receives a new message and sends an acknowledgment
       (/\ channel = {<<m, b>>}
        /\ m \in DataItems
        /\ b \in {0, 1}
        /\ b # receiverSeqBit
        /\ receiverBuffer' = <<m>>
        /\ receiverSeqBit' = b
        /\ channel' = {<<b>>})
    \/ \* Receiver receives a duplicate message and sends an acknowledgment for the last delivered bit
       (/\ channel = {<<m, b>>}
        /\ m \in DataItems
        /\ b \in {0, 1}
        /\ b = receiverSeqBit
        /\ UNCHANGED receiverBuffer
        /\ UNCHANGED receiverSeqBit
        /\ channel' = {<<b>>})
    \/ \* Acknowledgment is lost in transit
       (/\ channel = {b}
        /\ b \in {0, 1}
        /\ channel' = {}
        /\ UNCHANGED senderSeqBit
        /\ UNCHANGED senderBuffer
        /\ UNCHANGED receiverSeqBit
        /\ UNCHANGED receiverBuffer)
    \/ \* Receiver receives an acknowledgment (no effect on state)
       (/\ channel = {b}
        /\ b \in {0, 1}
        /\ channel' = {}
        /\ UNCHANGED senderSeqBit
        /\ UNCHANGED senderBuffer
        /\ UNCHANGED receiverSeqBit
        /\ UNCHANGED receiverBuffer)

Spec ==
    /\ Init
    /\ [][Next]_<<senderSeqBit, receiverSeqBit, channel, senderBuffer, receiverBuffer>>
    /\ WF_next(<<senderSeqBit, receiverSeqBit, channel, senderBuffer, receiverBuffer>>)

\* Safety properties
TypeOK ==
    /\ senderSeqBit \in {0, 1}
    /\ receiverSeqBit \in {0, 1}
    /\ channel \subseteq (DataItems \X {0, 1}) \cup ({0, 1})
    /\ senderBuffer \in DataItems
    /\ receiverBuffer \in SUBSET DataItems

NoDuplicates ==
    \/ receiverBuffer = <<>>
    \/ receiverBuffer \notin {<<m>> : m \in DataItems}

\* Liveness properties
Fairness ==
    WF_next(<<senderSeqBit, receiverSeqBit, channel, senderBuffer, receiverBuffer>>)

Delivery ==
    [](\/ receiverBuffer = <<>>
        \/ <>(receiverBuffer' = <<m>> /\ m \in DataItems))

Agreement ==
    [](\/ channel = {}
        \/ (channel = {b} => b = receiverSeqBit)
        \/ (channel = {<<m, b>>} => b # receiverSeqBit))

=============================================================================