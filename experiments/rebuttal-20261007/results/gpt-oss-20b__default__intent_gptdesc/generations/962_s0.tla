MODULE ABProtocol
EXTENDS Naturals, Sequences

CONSTANTS DataSet

(* Variables *)
VARIABLES senderBit, receiverLastDeliveredBit,
          pendingMessages, pendingAcks,
          currMsg, senderHasOutstanding,
          queue, delivered, sentData

vars == {senderBit, receiverLastDeliveredBit, pendingMessages,
         pendingAcks, currMsg, senderHasOutstanding,
         queue, delivered, sentData}

(* Types *)
Bit == {0,1}
Message == [data: DataSet, bit: Bit]

IsMessage(m) ==
  /\ m.data ∈ DataSet
  /\ m.bit ∈ Bit

TypeInv ==
  /\ senderBit ∈ Bit
  /\ receiverLastDeliveredBit ∈ Bit
  /\ ∀ m ∈ pendingMessages : IsMessage(m)
  /\ (currMsg = nil \/ IsMessage(currMsg))
  /\ queue ∈ Seq(DataSet)
  /\ delivered ∈ Seq(DataSet)
  /\ sentData ⊆ DataSet
  /\ senderHasOutstanding ∈ BOOLEAN

(* Initial state *)
Init ==
  /\ senderBit = 0
  /\ receiverLastDeliveredBit = 0
  /\ pendingMessages = {}
  /\ pendingAcks = {}
  /\ currMsg = nil
  /\ senderHasOutstanding = FALSE
  /\ queue \in Seq(DataSet)
  /\ delivered = <<>>
  /\ sentData = {}

(* Actions *)
SenderSend ==
  /\ ¬senderHasOutstanding
  /\ queue ≠ <<>>
  /\ LET d == Head(queue) IN
     /\ currMsg' = [data |-> d, bit |-> senderBit]
     /\ pendingMessages' = pendingMessages ∪ {currMsg'}
     /\ sentData' = sentData ∪ {d}
     /\ queue' = Tail(queue)
     /\ senderHasOutstanding' = TRUE
  /\ UNCHANGED <<senderBit, receiverLastDeliveredBit,
                 pendingAcks, delivered>>

SenderRetransmit ==
  /\ senderHasOutstanding
  /\ currMsg ≠ nil
  /\ LET m == currMsg IN
     /\ pendingMessages' = pendingMessages ∪ {m}
     /\ sentData' = sentData ∪ {m.data}
  /\ UNCHANGED <<senderBit, receiverLastDeliveredBit,
                 pendingAcks, queue, delivered>>

SenderAckReceive ==
  /\ ∃ b ∈ pendingAcks : b = senderBit
  /\ pendingAcks' = pendingAcks \ {senderBit}
  /\ senderHasOutstanding' = FALSE
  /\ senderBit' = 1 - senderBit
  /\ currMsg' = nil
  /\ UNCHANGED <<receiverLastDeliveredBit, queue,
                 delivered, pendingMessages>>

ReceiverReceive ==
  /\ ∃ m ∈ pendingMessages : TRUE
  /\ LET m == CHOOSE x \in pendingMessages : TRUE IN
     /\ pendingMessages' = pendingMessages \ {m}
     /\ IF m.bit # receiverLastDeliveredBit THEN
          delivered' = Append(delivered, m.data)
          /\ receiverLastDeliveredBit' = m.bit
        ELSE
          delivered' = delivered
        ENDIF
     /\ pendingAcks' = pendingAcks ∪ {m.bit}
  /\ UNCHANGED <<senderBit, senderHasOutstanding,
                 currMsg, queue>>

MessageLoss ==
  /\ ∃ m ∈ pendingMessages : TRUE
  /\ LET m == CHOOSE x \in pendingMessages : TRUE IN
     /\ pendingMessages' = pendingMessages \ {m}
  /\ UNCHANGED <<senderBit, receiverLastDeliveredBit,
                 senderHasOutstanding, currMsg, queue,
                 delivered, pendingAcks>>

AckLoss ==
  /\ ∃ b ∈ pendingAcks : TRUE
  /\ LET b == CHOOSE x \in pendingAcks : TRUE IN
     /\ pendingAcks' = pendingAcks \ {b}
  /\ UNCHANGED <<senderBit, receiverLastDeliveredBit,
                 senderHasOutstanding, currMsg, queue,
                 delivered, pendingMessages>>

Next ==
  SenderSend \/ SenderRetransmit \/ SenderAckReceive \/ ReceiverReceive \/ MessageLoss \/ AckLoss

(* Fairness conditions *)
WF_Recv == WeakFairness(ReceiverReceive)
WF_Ack == WeakFairness(SenderAckReceive)

Fairness == WF_Recv /\ WF_Ack

(* Safety invariants *)
DeliveredInSentData ==
  ∀ i ∈ 1..Len(delivered) : delivered[i] ∈ sentData

NoDupDelivered ==
  ∀ i,j ∈ 1..Len(delivered) :
