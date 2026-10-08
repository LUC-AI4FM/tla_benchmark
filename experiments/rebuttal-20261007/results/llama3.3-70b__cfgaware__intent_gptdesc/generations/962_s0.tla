--------------------------- MODULE ABCSpec ---------------------------
EXTENDS Integers, Sequences

CONSTANT Data
VARIABLE senderSeqBit, receiverSeqBit, 
         senderOutstandingMsg, receiverDeliveredValue,
         channelMessages, channelAcks

TypeInv == 
  /\ senderSeqBit \in {0, 1}
  /\ receiverSeqBit \in {0, 1}
  /\ senderOutstandingMsg \in Data
  /\ receiverDeliveredValue \in Data
  /\ channelMessages \subseteq [Data][{seqBit |-> {0, 1}}]
  /\ channelAcks \subseteq {0, 1}

Init == 
  /\ senderSeqBit = 0
  /\ receiverSeqBit = 0
  /\ senderOutstandingMsg = <<>>
  /\ receiverDeliveredValue = <<>>
  /\ channelMessages = {}
  /\ channelAcks = {}

NextSender == 
  /\ senderOutstandingMsg' = Data
  /\ senderSeqBit' = IF senderSeqBit = 0 THEN 1 ELSE 0
  /\ UNCHANGED <<receiverSeqBit, receiverDeliveredValue, channelMessages, channelAcks>>

Send == 
  /\ ~ (senderOutstandingMsg \in [m |-> s IN channelMessages])
  /\ channelMessages' = channelMessages \cup {[senderOutstandingMsg |-> senderSeqBit]}
  /\ UNCHANGED <<senderSeqBit, receiverSeqBit, receiverDeliveredValue, senderOutstandingMsg, channelAcks>>

Receive == 
  /\ ~ (channelMessages = {})
  /\ \E msg \in Data, seq IN {0, 1} : 
      {[msg |-> seq] \in channelMessages
       /\ msg' = msg
       /\ IF receiverSeqBit = seq THEN 
            receiverDeliveredValue' = msg'
         ELSE 
            receiverDeliveredValue' = receiverDeliveredValue
       /\ receiverSeqBit' = IF receiverSeqBit = seq THEN IF seq = 0 THEN 1 ELSE 0 ELSE receiverSeqBit
       /\ channelMessages' = channelMessages \ {[msg |-> seq]}
       /\ UNCHANGED <<senderSeqBit, senderOutstandingMsg, channelAcks>>}

Ack == 
  /\ ~ (channelAcks = {})
  /\ \E ack IN {0, 1} : 
      {ack \in channelAcks
       /\ IF senderSeqBit = ack THEN 
            senderOutstandingMsg' = <<>>
         ELSE 
            senderOutstandingMsg' = senderOutstandingMsg
       /\ channelAcks' = channelAcks \ {ack}
       /\ UNCHANGED <<receiverSeqBit, receiverDeliveredValue, channelMessages>>}

Next == NextSender \/ Send \/ Receive \/ Ack

Spec == Init /\ [][Next]_<<senderSeqBit, receiverSeqBit, senderOutstandingMsg, receiverDeliveredValue, channelMessages, channelAcks>>

THEOREM Spec => []TypeInv
=============================================================================