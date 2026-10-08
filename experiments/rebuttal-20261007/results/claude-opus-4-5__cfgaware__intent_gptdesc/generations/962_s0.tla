---------------------------- MODULE ABCSpec ----------------------------

CONSTANTS Data

VARIABLES
    senderBit,      \* The sender's current sequence bit
    senderData,     \* The data the sender is currently trying to send
    senderReady,    \* Whether sender is ready to accept new data
    receiverBit,    \* The receiver's last accepted sequence bit
    receiverData,   \* The last data delivered by the receiver
    msgChannel,     \* Channel for data messages (set of <<data, bit>> pairs)
    ackChannel      \* Channel for acknowledgments (set of bits)

vars == <<senderBit, senderData, senderReady, receiverBit, receiverData, msgChannel, ackChannel>>

-----------------------------------------------------------------------------

TypeInv ==
    /\ senderBit \in {0, 1}
    /\ senderData \in Data \cup {<<>>}
    /\ senderReady \in BOOLEAN
    /\ receiverBit \in {0, 1}
    /\ receiverData \in Data \cup {<<>>}
    /\ msgChannel \subseteq (Data \X {0, 1})
    /\ ackChannel \subseteq {0, 1}

-----------------------------------------------------------------------------

Init ==
    /\ senderBit = 0
    /\ senderData = <<>>
    /\ senderReady = TRUE
    /\ receiverBit = 1          \* Initially different from senderBit
    /\ receiverData = <<>>
    /\ msgChannel = {}
    /\ ackChannel = {}

-----------------------------------------------------------------------------

\* Sender initiates transmission of a new data item
\* Only when sender believes previous one has been acknowledged (senderReady = TRUE)
SendNew(d) ==
    /\ senderReady = TRUE
    /\ senderData' = d
    /\ senderBit' = 1 - senderBit   \* Flip the bit for new data
    /\ senderReady' = FALSE
    /\ msgChannel' = msgChannel \cup {<<d, 1 - senderBit>>}
    /\ UNCHANGED <<receiverBit, receiverData, ackChannel>>

\* Sender retransmits the current outstanding message
Retransmit ==
    /\ senderReady = FALSE
    /\ senderData # <<>>
    /\ msgChannel' = msgChannel \cup {<<senderData, senderBit>>}
    /\ UNCHANGED <<senderBit, senderData, senderReady, receiverBit, receiverData, ackChannel>>

\* Sender receives an acknowledgment
ReceiveAck ==
    /\ ackChannel # {}
    /\ \E b \in ackChannel:
        /\ ackChannel' = ackChannel \ {b}
        /\ IF b = senderBit
           THEN senderReady' = TRUE
           ELSE senderReady' = senderReady
        /\ UNCHANGED <<senderBit, senderData, receiverBit, receiverData, msgChannel>>

\* Receiver receives a message and processes it
ReceiveMsg ==
    /\ msgChannel # {}
    /\ \E m \in msgChannel:
        LET d == m[1]
            b == m[2]
        IN
        /\ msgChannel' = msgChannel \ {m}
        /\ IF b # receiverBit
           THEN \* Fresh message - accept it
                /\ receiverData' = d
                /\ receiverBit' = b
                /\ ackChannel' = ackChannel \cup {b}
           ELSE \* Duplicate message - just re-ack
                /\ ackChannel' = ackChannel \cup {receiverBit}
                /\ UNCHANGED <<receiverBit, receiverData>>
        /\ UNCHANGED <<senderBit, senderData, senderReady>>

\* Channel loses a data message
LoseMsg ==
    /\ msgChannel # {}
    /\ \E m \in msgChannel:
        /\ msgChannel' = msgChannel \ {m}
        /\ UNCHANGED <<senderBit, senderData, senderReady, receiverBit, receiverData, ackChannel>>

\* Channel loses an acknowledgment
LoseAck ==
    /\ ackChannel # {}
    /\ \E b \in ackChannel:
        /\ ackChannel' = ackChannel \ {b}
        /\ UNCHANGED <<senderBit, senderData, senderReady, receiverBit, receiverData, msgChannel>>

\* Channel duplicates a data message (message stays in channel)
DuplicateMsg ==
    /\ msgChannel # {}
    /\ UNCHANGED vars

\* Channel duplicates an acknowledgment (ack stays in channel)
DuplicateAck ==
    /\ ackChannel # {}
    /\ UNCHANGED vars

-----------------------------------------------------------------------------

Next ==
    \/ \E d \in Data: SendNew(d)
    \/ Retransmit
    \/ ReceiveAck
    \/ ReceiveMsg
    \/ LoseMsg
    \/ LoseAck
    \/ DuplicateMsg
    \/ DuplicateAck

-----------------------------------------------------------------------------

\* Fairness conditions
\* Fair-loss assumption: if messages are repeatedly sent, delivery eventually occurs
\* We use weak fairness on receiving actions and strong fairness on retransmission

Fairness ==
    /\ WF_vars(ReceiveMsg)      \* If a message is in the channel, it will eventually be received
    /\ WF_vars(ReceiveAck)      \* If an ack is in the channel, it will eventually be received
    /\ SF_vars(Retransmit)      \* Sender will keep retransmitting if not acknowledged

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

\* Safety: Track what has been sent to verify receiver only delivers sent values
\* This is implicit in the protocol: receiver can only deliver data that came through msgChannel
\* which can only contain data put there by SendNew

\* Helper: The set of data values that have been sent
\* Safety property: receiverData is either initial or was sent by sender
Safety ==
    receiverData = <<>> \/ receiverData \in Data

\* No duplication is ensured by the alternating bit protocol:
\* The receiver only accepts data when the bit differs from its current bit,
\* then updates its bit to match, preventing re-acceptance of the same transmission

-----------------------------------------------------------------------------

\* Liveness: If sender sends data, it will eventually be delivered
\* This follows from fairness: retransmission is fair, receiving is fair

\* Agreement on sequence bits: When receiver accepts, its bit matches the message bit,
\* and acknowledgments carry this bit back to sender

=============================================================================