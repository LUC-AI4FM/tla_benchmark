------------------------------ MODULE AlternatingBit ------------------------------
(***************************************************************************)
(* Alternating Bit Protocol: a sender and a receiver communicate over two  *)
(* unreliable channels.                                                    *)
(*   msgC : sender -> receiver, carries <<bit, data>> frames               *)
(*   ackC : receiver -> sender, carries acknowledgment bits                *)
(*                                                                         *)
(* The channels may LOSE, DUPLICATE and REORDER frames. They never corrupt *)
(* a frame. Reordering is limited to frames that carry the same control    *)
(* bit. ABP cannot be correct under unrestricted reordering: a stale frame *)
(* overtaking a newer frame with the opposite bit causes an undetectable   *)
(* duplicate.                                                              *)
(*                                                                         *)
(* Observable actions:                                                     *)
(*   Send(d)     - sender offers a new data value d                        *)
(*   Retransmit  - sender retransmits the outstanding frame                *)
(*   RcvMsg      - receiver takes a frame from the channel                 *)
(*   Deliver     - receiver delivers an accepted value to its user         *)
(*   SendAck     - receiver acknowledges the last accepted bit             *)
(*   RcvAck      - sender takes an acknowledgment from the channel         *)
(*                                                                         *)
(* The history variables sent and delivered record the observable          *)
(* behaviour. The invariants are stated over them.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data,      \* arbitrary finite set of message values
          NoData,    \* placeholder meaning "no value"
          ChanCap    \* bound on channel length (keeps the model finite)

ASSUME DataAssump    == IsFiniteSet(Data) /\ Data # {}
ASSUME NoDataAssump  == NoData \notin Data
ASSUME ChanCapAssump == ChanCap \in Nat \ {0}

VARIABLES
  sBit,       \* sender's current control bit
  sData,      \* data value currently outstanding at the sender
  sBusy,      \* TRUE iff the sender awaits an acknowledgment
  rBit,       \* bit the receiver expects next
  rBuf,       \* value accepted by the receiver but not yet delivered
  msgC,       \* data channel (sender -> receiver)
  ackC,       \* acknowledgment channel (receiver -> sender)
  sent,       \* history: sequence of values offered by the sender
  delivered   \* history: sequence of values delivered by the receiver

vars == <<sBit, sData, sBusy, rBit, rBuf, msgC, ackC, sent, delivered>>

Bits    == {0, 1}
Flip(b) == 1 - b
Frames  == Bits \X Data

(* Generic channel manipulations *)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
DupAt(s, i)    == SubSeq(s, 1, i) \o <<s[i]>> \o SubSeq(s, i + 1, Len(s))
SwapAt(s, i)   == [s EXCEPT ![i] = s[i + 1], ![i + 1] = s[i]]

Range(s) == { s[i] : i \in 1..Len(s) }

-----------------------------------------------------------------------------
TypeOK ==
  /\ sBit      \in Bits
  /\ sData     \in Data \cup {NoData}
  /\ sBusy     \in BOOLEAN
  /\ rBit      \in Bits
  /\ rBuf      \in Data \cup {NoData}
  /\ msgC      \in Seq(Frames)
  /\ ackC      \in Seq(Bits)
  /\ sent      \in Seq(Data)
  /\ delivered \in Seq(Data)

Init ==
  /\ sBit      = 0
  /\ sData     = NoData
  /\ sBusy     = FALSE
  /\ rBit      = 0
  /\ rBuf      = NoData
  /\ msgC      = << >>
  /\ ackC      = << >>
  /\ sent      = << >>
  /\ delivered = << >>

-----------------------------------------------------------------------------
(*************************** Sender ****************************************)

\* Offer a new value. If the channel is full, the first transmission is lost.
Send(d) ==
  /\ ~sBusy
  /\ sBusy' = TRUE
  /\ sData' = d
  /\ sent'  = Append(sent, d)
  /\ msgC'  = IF Len(msgC) < ChanCap
                THEN Append(msgC, <<sBit, d>>)
                ELSE msgC
  /\ UNCHANGED <<sBit, rBit, rBuf, ackC, delivered>>

\* Retransmit the outstanding frame.
Retransmit ==
  /\ sBusy
  /\ Len(msgC) < ChanCap
  /\ msgC' = Append(msgC, <<sBit, sData>>)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, ackC, sent, delivered>>

\* Consume an acknowledgment. A matching ack completes the transfer and
\* flips the bit. Any other ack is discarded.
RcvAck ==
  /\ ackC # << >>
  /\ ackC' = Tail(ackC)
  /\ IF sBusy /\ Head(ackC) = sBit
       THEN /\ sBusy' = FALSE
            /\ sBit'  = Flip(sBit)
       ELSE UNCHANGED <<sBusy, sBit>>
  /\ UNCHANGED <<sData, rBit, rBuf, msgC, sent, delivered>>

\* Receipt of the acknowledgment the sender is waiting for.
RcvGoodAck ==
  /\ RcvAck
  /\ sBusy
  /\ Head(ackC) = sBit

(*************************** Receiver **************************************)

\* Consume a frame. A frame with the expected bit is accepted and the
\* expected bit flips. Any other frame is a duplicate and is discarded.
RcvMsg ==
  /\ rBuf = NoData
  /\ msgC # << >>
  /\ msgC' = Tail(msgC)
  /\ IF Head(msgC)[1] = rBit
       THEN /\ rBuf' = Head(msgC)[2]
            /\ rBit' = Flip(rBit)
       ELSE UNCHANGED <<rBuf, rBit>>
  /\ UNCHANGED <<sBit, sData, sBusy, ackC, sent, delivered>>

\* Receipt of a frame carrying the expected bit.
RcvGoodMsg ==
  /\ RcvMsg
  /\ Head(msgC)[1] = rBit

\* Deliver the accepted value to the receiving user.
Deliver ==
  /\ rBuf # NoData
  /\ delivered' = Append(delivered, rBuf)
  /\ rBuf'      = NoData
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, msgC, ackC, sent>>

\* Acknowledge the last accepted (and delivered) bit.
SendAck ==
  /\ rBuf = NoData
  /\ Len(ackC) < ChanCap
  /\ ackC' = Append(ackC, Flip(rBit))
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, msgC, sent, delivered>>

(*************************** Channel ***************************************)

LoseMsg ==
  /\ \E i \in 1..Len(msgC) : msgC' = RemoveAt(msgC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, ackC, sent, delivered>>

DupMsg ==
  /\ Len(msgC) < ChanCap
  /\ \E i \in 1..Len(msgC) : msgC' = DupAt(msgC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, ackC, sent, delivered>>

ReorderMsg ==
  /\ \E i \in 1..(Len(msgC) - 1) :
        /\ msgC[i][1] = msgC[i + 1][1]
        /\ msgC' = SwapAt(msgC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, ackC, sent, delivered>>

LoseAck ==
  /\ \E i \in 1..Len(ackC) : ackC' = RemoveAt(ackC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, msgC, sent, delivered>>

DupAck ==
  /\ Len(ackC) < ChanCap
  /\ \E i \in 1..Len(ackC) : ackC' = DupAt(ackC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, msgC, sent, delivered>>

ReorderAck ==
  /\ \E i \in 1..(Len(ackC) - 1) :
        /\ ackC[i] = ackC[i + 1]
        /\ ackC' = SwapAt(ackC, i)
  /\ UNCHANGED <<sBit, sData, sBusy, rBit, rBuf, msgC, sent, delivered>>

-----------------------------------------------------------------------------
SenderStep   == (\E d \in Data : Send(d)) \/ Retransmit \/ RcvAck
ReceiverStep == RcvMsg \/ Deliver \/ SendAck
ChannelStep  == LoseMsg \/ DupMsg \/ ReorderMsg \/ LoseAck \/ DupAck \/ ReorderAck

Next == SenderStep \/ ReceiverStep \/ ChannelStep

(***************************************************************************)
(* Fairness: neither process may be starved.                               *)
(*   - Weak fairness on every process step: retransmit, take frames or     *)
(*     acks, deliver, and acknowledge.                                     *)
(*   - Strong fairness on receiving a useful frame or ack. This captures   *)
(*     the requirement that a channel which repeatedly offers a good copy  *)
(*     eventually delivers it.                                             *)
(* Sending of new values (Send) is not forced. The sender offers data only *)
(* when it intends to.                                                     *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(Retransmit)
  /\ WF_vars(RcvAck)
  /\ WF_vars(RcvMsg)
  /\ WF_vars(Deliver)
  /\ WF_vars(SendAck)
  /\ SF_vars(RcvGoodMsg)
  /\ SF_vars(RcvGoodAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety ****************************************)

\* Integrity: every delivered value was previously sent.
Integrity ==
  \A i \in 1..Len(delivered) : delivered[i] \in Range(sent)

\* No spurious duplicates: the receiver never delivers more items than the
\* sender has issued, so no item is delivered twice without an
\* intervening new send.
NoSpuriousDuplicate ==
  Len(delivered) <= Len(sent)

\* Stronger: delivered values form an in-order prefix of the sent values.
InOrderDelivery ==
  /\ NoSpuriousDuplicate
  /\ delivered = SubSeq(sent, 1, Len(delivered))

\* Action form: each delivery step corresponds to a fresh send.
NoDuplicateDeliveryStep ==
  [][ Len(delivered') > Len(delivered) => Len(delivered') <= Len(sent') ]_vars

Safety == TypeOK /\ Integrity /\ NoSpuriousDuplicate /\ InOrderDelivery

THEOREM SafetyThm == Spec => []Safety

(*************************** Liveness **************************************)

(***************************************************************************)
(* Channel assumption. If the protocol is stuck in some phase, the channel *)
(* keeps offering a copy that makes progress: a fresh frame while the      *)
(* receiver awaits it, or a matching ack while the sender awaits it. In    *)
(* other words, not all copies are lost or masked forever.                 *)
(***************************************************************************)
ChannelLive ==
  /\ []<>( ~sBusy \/ rBit # sBit \/ ENABLED <<RcvGoodMsg>>_vars )
  /\ []<>( ~sBusy \/ rBit = sBit \/ ENABLED <<RcvGoodAck>>_vars )

\* Every outstanding transmission is eventually acknowledged.
SenderProgress ==
  ChannelLive => (sBusy ~> ~sBusy)

\* Every value the sender offers is eventually delivered by the receiver.
EventualDelivery ==
  ChannelLive =>
    \A n \in Nat \ {0} : (Len(sent) >= n) ~> (Len(delivered) >= n)

\* An accepted value is always eventually delivered (receiver not starved).
ReceiverProgress ==
  (rBuf # NoData) ~> (rBuf = NoData)

THEOREM LivenessThm ==
  Spec => (SenderProgress /\ EventualDelivery /\ ReceiverProgress)

=============================================================================