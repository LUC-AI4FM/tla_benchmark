---------------------------- MODULE ABCSpec ----------------------------

CONSTANTS Data

VARIABLES senderSeqBit, receiverSeqBit, lastDelivered, channel

ASSUME DATA_INVARIANT == Data \subseteq Nat /\ Data /= {}

(*--algorithm alternating_bit_protocol

variables 
    senderSeqBit = 0,
    receiverSeqBit = 0,
    lastDelivered = <<>>,
    channel = {}

fair process (Sender)
begin
    while TRUE do
        with dataItem \in Data do
            await channel[dataItem, senderSeqBit] \notin channel
            channel := channel \cup {[dataItem, senderSeqBit]}
            await [ack \in channel |-> ack[1] = senderSeqBit]
            channel := channel \ {ack \in channel |-> ack[1] = senderSeqBit}
            senderSeqBit := 1 - senderSeqBit
    end while
end process;

fair process (Receiver)
begin
    while TRUE do
        await [msg \in channel |-> msg[2] <> receiverSeqBit]
        with msg \in channel |-> msg[2] <> receiverSeqBit do
            lastDelivered := Append(lastDelivered, msg[0])
            channel := channel \ {msg}
            channel := channel \cup {[msg[1], receiverSeqBit]}
            receiverSeqBit := 1 - receiverSeqBit
    end while
end process;

end algorithm;)

TypeInv ==
    /\ senderSeqBit \in {0, 1}
    /\ receiverSeqBit \in {0, 1}
    /\ lastDelivered \in Seq(Data)
    /\ channel \subseteq [Data -> {0, 1}] \cup [{0, 1} -> {0, 1}]
    
WF_Send ==
    WF_next(Send)

WF_Receive ==
    WF_next(Receive)

Spec == 
    /\ TypeInv
    /\ Init
    /\ [][Next]_<<senderSeqBit, receiverSeqBit, lastDelivered, channel>>
    /\ SF_Send
    /\ SF_Receive

THEOREM Spec => []TypeInv

======================================================================