```tla
MODULE AlternatingBitProtocol

EXTENDS Integers, Sequences

CONSTANTS Data, SenderSeqno, ReceiverSeqno
VARIABLES senderData, senderSeqno, receiverData, receiverSeqno, 
          channelMessages, channelAcks, deliveredValues

Init ==
  /\ senderData = <<>>
  /\ senderSeqno = 0
  /\ receiverData = <<>>
  /\ receiverSeqno = 0
  /\ channelMessages = {}
  /\ channelAcks = {}
  /\ deliveredValues = {}

Next ==
  \/ SendMessage
  \/ ReceiveMessage
  \/ SendAck
  \/ ReceiveAck

SendMessage ==
  /\ senderData # <<>> 
  /\ channelMessages' = channelMessages \cup {<<senderData[1], senderSeqno>>}
  /\ senderData' = Tail(senderData)
  /\ senderSeqno' = IF senderSeqno = 0 THEN 1 ELSE 0
  /\ UNCHANGED <<receiverData, receiverSeqno, channelAcks, deliveredValues>>

ReceiveMessage ==
  /\ channelMessages # {}
  /\ LET message == CHOOSE m \in channelMessages : TRUE IN
    /\ (message[2] # receiverSeqno) 
    /\ receiverData' = Append(receiverData, message[1])
    /\ receiverSeqno' = message[2]
    /\ deliveredValues' = deliveredValues \cup {message[1]}
    /\ channelMessages' = channelMessages \ {message}
    /\ UNCHANGED <<senderData, senderSeqno, channelAcks>>

SendAck ==
  /\ receiverData # <<>>
  /\ channelAcks' = channelAcks \cup {receiverSeqno}
  /\ UNCHANGED <<senderData, senderSeqno, receiverData, receiverSeqno, channelMessages, deliveredValues>>

ReceiveAck ==
  /\ channelAcks # {}
  /\ LET ack == CHOOSE a \in channelAcks : TRUE IN
    /\ (ack = senderSeqno)
    /\ channelAcks' = channelAcks \ {ack}
    /\ UNCHANGED <<senderData, receiverData, receiverSeqno, channelMessages, deliveredValues>>
    /\ IF senderData # <<>> THEN senderSeqno' = IF senderSeqno = 0 THEN 1 ELSE 0 ELSE senderSeqno' = senderSeqno

Spec ==
  /\ Init
  /\ [][Next]_<<senderData, senderSeqno, receiverData, receiverSeqno, channelMessages, channelAcks, deliveredValues>>
  /\ WF_Vars(ReceiveMessage)
  /\ SF_Vars(SendAck)

TypeInvariant ==
  /\ senderData \in Seq(Data)
  /\ senderSeqno \in {0, 1}
  /\ receiverData \in Seq(Data)
  /\ receiverSeqno \in {0, 1}
  /\ channelMessages \subseteq {<<d, s>> : d \in Data /\ s \in {0, 1}}
  /\ channelAcks \subseteq {0, 1}
  /\ deliveredValues \subseteq Data

THEOREM Spec => []TypeInvariant
THEOREM Spec => [](NoDup(deliveredValues))
THEOREM Spec => [](DeliveredImpliesSent)
THEOREM Spec => <>[]DeliveredValues = Data

NoDup(vs) == vs = Union({{v} : v \in vs})

DeliveredImpliesSent ==
  deliveredValues \subseteq {d : <<d, _>> \in [channelMessages \cup {<<m[1], m[2]>> : m \in channelAcks}]}

DeliveredValues == deliveredValues
```