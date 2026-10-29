--------------------------- MODULE AlternatingBit ---------------------------
(***************************************************************************)
(* Alternating-bit reliable data transfer between a Sender and a Receiver  *)
(* over lossy channels.                                                    *)
(*                                                                         *)
(* Each direction holds an unbounded but always finite sequence of         *)
(* in-flight items. Any single item may be dropped at any time. Delivered  *)
(* items are never corrupted.                                              *)
(*                                                                         *)
(* Channel order: dropping an item keeps the order of the other items.     *)
(* Receivers consume from the head, so the channels are lossy FIFO. The    *)
(* alternating-bit protocol is only correct when the channels do not       *)
(* reorder. With arbitrary reordering, a stale acknowledgment can be       *)
(* mistaken for a fresh one, which breaks the safety properties below.     *)
(* Order preservation is therefore part of this model.                     *)
(*                                                                         *)
(* History variables (sent, delivered) record the sender's committed data  *)
(* choices and the receiver's accepted data. They are used only to state   *)
(* the properties.                                                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Data,        \* finite set of possible data values
          MaxLen       \* bound used only by the optional TLC constraint

ASSUME DataAssump == Data # {} /\ IsFiniteSetHelper == TRUE
ASSUME MaxLenAssump == MaxLen \in Nat

NoData == CHOOSE v : v \notin Data

Bits == {0, 1}
Flip(b) == 1 - b

VARIABLES
  sBit,       \* sender's current sequence bit
  sData,      \* data value the sender is currently trying to transfer
  rBit,       \* receiver's last-seen (last accepted) bit
  rData,      \* receiver's most recently delivered data value
  msgs,       \* in-flight data messages, sender -> receiver: <<data, bit>>
  acks,       \* in-flight acknowledgments, receiver -> sender: bit
  sent,       \* history: sequence of data values committed by the sender
  delivered   \* history: sequence of data values accepted by the receiver

vars == <<sBit, sData, rBit, rData, msgs, acks, sent, delivered>>

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

Last(s) == s[Len(s)]

IsPrefix(p, s) == Len(p) <= Len(s) /\ p = SubSeq(s, 1, Len(p))

-----------------------------------------------------------------------------
TypeOK ==
  /\ sBit \in Bits
  /\ sData \in Data
  /\ rBit \in Bits
  /\ rData \in Data \cup {NoData}
  /\ msgs \in Seq(Data \X Bits)
  /\ acks \in Seq(Bits)
  /\ sent \in Seq(Data)
  /\ delivered \in Seq(Data)

(***************************************************************************)
(* Initial state. The receiver's last-seen bit starts at 0, and the sender *)
(* starts with bit 1, so the sender's first message counts as "new".       *)
(***************************************************************************)
Init ==
  /\ sBit = 1
  /\ sData \in Data
  /\ rBit = 0
  /\ rData = NoData
  /\ msgs = << >>
  /\ acks = << >>
  /\ sent = << sData >>
  /\ delivered = << >>

-----------------------------------------------------------------------------
(* The sender sends or retransmits its current message. *)
SndSend ==
  /\ msgs' = Append(msgs, <<sData, sBit>>)
  /\ UNCHANGED <<sBit, sData, rBit, rData, acks, sent, delivered>>

(* The sender handles an acknowledgment. If the ack matches the current   *)
(* bit, the message was accepted. The sender then flips its bit and       *)
(* commits to a new data value. Otherwise the ack is stale and discarded. *)
SndRcvAck ==
  /\ acks # << >>
  /\ acks' = Tail(acks)
  /\ IF Head(acks) = sBit
       THEN \E d \in Data :
              /\ sData' = d
              /\ sBit' = Flip(sBit)
              /\ sent' = Append(sent, d)
       ELSE UNCHANGED <<sBit, sData, sent>>
  /\ UNCHANGED <<rBit, rData, msgs, delivered>>

(* The receiver sends or retransmits an ack carrying its last accepted bit. *)
RcvSendAck ==
  /\ acks' = Append(acks, rBit)
  /\ UNCHANGED <<sBit, sData, rBit, rData, msgs, sent, delivered>>

(* The receiver handles a data message. It accepts the message only if    *)
(* the bit differs from the last-seen bit. Otherwise the message is a     *)
(* duplicate and is discarded.                                            *)
RcvData ==
  /\ msgs # << >>
  /\ msgs' = Tail(msgs)
  /\ LET d == Head(msgs)[1]
         b == Head(msgs)[2]
     IN  IF b # rBit
           THEN /\ rBit' = b
                /\ rData' = d
                /\ delivered' = Append(delivered, d)
           ELSE UNCHANGED <<rBit, rData, delivered>>
  /\ UNCHANGED <<sBit, sData, acks, sent>>

(* Loss of a single in-flight data message. *)
LoseMsg ==
  /\ \E i \in 1..Len(msgs) : msgs' = RemoveAt(msgs, i)
  /\ UNCHANGED <<sBit, sData, rBit, rData, acks, sent, delivered>>

(* Loss of a single in-flight acknowledgment. *)
LoseAck ==
  /\ \E i \in 1..Len(acks) : acks' = RemoveAt(acks, i)
  /\ UNCHANGED <<sBit, sData, rBit, rData, msgs, sent, delivered>>

Next ==
  \/ SndSend
  \/ SndRcvAck
  \/ RcvSendAck
  \/ RcvData
  \/ LoseMsg
  \/ LoseAck

(***************************************************************************)
(* Fairness.                                                               *)
(* - The sender's and receiver's sending actions are always enabled, so    *)
(*   they get weak fairness.                                               *)
(* - Loss can disable the receiving actions again and again. "Losses do    *)
(*   not persist forever" is therefore modeled with strong fairness on the *)
(*   receiving actions. If an item is in flight infinitely often, some     *)
(*   item is eventually received.                                          *)
(* - Loss actions have no fairness.                                        *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(SndSend)
  /\ WF_vars(RcvSendAck)
  /\ SF_vars(RcvData)
  /\ SF_vars(SndRcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** SAFETY PROPERTIES *****************************)

(* The receiver only delivers values the sender actually sent. *)
DeliveredWasSent ==
  rData # NoData => \E i \in 1..Len(sent) : sent[i] = rData

(* Delivered values follow the sender's committed choices, in order. The  *)
(* receiver is at most one value behind the sender.                       *)
NoSpuriousData ==
  /\ IsPrefix(delivered, sent)
  /\ Len(sent) - Len(delivered) \in {0, 1}
  /\ (delivered # << >>) => rData = Last(delivered)
  /\ (delivered = << >>) => rData = NoData

(* Non-duplication. Each acceptance consumes a distinct sender commitment.*)
(* So two consecutive equal deliveries happen only when the sender        *)
(* intentionally committed the same value twice in a row, across a bit    *)
(* toggle.                                                                *)
NoDuplication ==
  \A i \in 1..(Len(delivered) - 1) :
     delivered[i] = delivered[i + 1] => sent[i] = sent[i + 1]

(* Bit alternation. Both bits track the parity of their history. The      *)
(* receiver is caught up exactly when the bits agree. Every in-flight     *)
(* message that carries the sender's current bit carries the current data.*)
BitAlternation ==
  /\ sBit = Len(sent) % 2
  /\ rBit = Len(delivered) % 2
  /\ (rBit = sBit) <=> (Len(delivered) = Len(sent))
  /\ \A i \in 1..Len(msgs) : msgs[i][2] = sBit => msgs[i][1] = sData
  /\ (rBit # sBit) => \A i \in 1..Len(acks) : acks[i] # sBit

(* The receiver changes its bit only by accepting a message with a        *)
(* different bit, and every such acceptance extends the delivered history.*)
AcceptOnlyOnBitChange ==
  [][ (rBit' # rBit) <=> (Len(delivered') = Len(delivered) + 1) ]_vars

(* The sender changes its bit only by committing to a new value. *)
SenderToggleOnlyOnAck ==
  [][ (sBit' # sBit) <=> (Len(sent') = Len(sent) + 1) ]_vars

Invariants ==
  /\ TypeOK
  /\ DeliveredWasSent
  /\ NoSpuriousData
  /\ NoDuplication
  /\ BitAlternation

-----------------------------------------------------------------------------
(*************************** LIVENESS PROPERTIES ***************************)

(* Every message the sender commits to, with its data and bit, is         *)
(* eventually accepted by the receiver.                                   *)
MessageEventuallyAccepted ==
  \A d \in Data, b \in Bits :
     (sData = d /\ sBit = b /\ rBit # b) ~> (rBit = b /\ rData = d)

(* After the receiver accepts, the sender eventually observes the ack and *)
(* moves on.                                                              *)
AckEventuallyObserved ==
  \A b \in Bits : (rBit = b /\ sBit = b) ~> (sBit # b)

(* Overall progress. Every committed value is eventually delivered, and   *)
(* the sender keeps committing new values.                                *)
Progress ==
  \A n \in Nat :
     /\ (Len(sent) = n) ~> (Len(delivered) >= n)
     /\ (Len(delivered) = n) ~> (Len(sent) > n)

-----------------------------------------------------------------------------
(* Optional state constraint for finite model checking with TLC. *)
StateConstraint ==
  /\ Len(msgs) <= MaxLen
  /\ Len(acks) <= MaxLen
  /\ Len(sent) <= MaxLen

THEOREM Spec => []Invariants
THEOREM Spec => AcceptOnlyOnBitChange /\ SenderToggleOnlyOnAck
THEOREM Spec => MessageEventuallyAccepted /\ AckEventuallyObserved /\ Progress
=============================================================================