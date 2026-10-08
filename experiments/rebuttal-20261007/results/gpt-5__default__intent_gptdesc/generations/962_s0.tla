---- MODULE AlternatingBit ----
EXTENDS Naturals, Sequences

(*
  Alternating-bit reliable data-transfer protocol between a single sender and receiver
  over unreliable channels that may lose, duplicate, and reorder messages (no corruption).
*)

CONSTANTS
  DSet,     \* Set of data items
  ToSend    \* Sequence of data items to be transmitted (possibly infinite)

ASSUME ToSend \in Seq(DSet)

\* Basic sets and records
Bits == {0, 1}
Msg  == [v : DSet, b : Bits]
Ack  == [b : Bits]

\* Helper sequence operators
Append(s, e) == s \o << e >>
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

\* Variables
VARIABLES
  sBit,         \* Sender's current bit to tag the outstanding message
  rBit,         \* Receiver's last-delivered bit
  sCur,         \* Index (in ToSend) of the currently outstanding item, or 0 if none
  nextToSend,   \* Index (in ToSend) of the next not-yet-started item = if sCur=0 then DeliveredLen+1 else sCur
  sOut,         \* Record holding the currently outstanding message contents (if any)
  delivered,    \* Sequence of items delivered by the receiver (in order)
  chD,          \* Unreliable data channel: sequence of Msg records
  chA           \* Unreliable ack channel: sequence of Ack records

vars == << sBit, rBit, sCur, nextToSend, sOut, delivered, chD, chA >>

\* Initial state
Init ==
  /\ sBit \in Bits
  /\ rBit = 1 - sBit
  /\ sCur = 0
  /\ nextToSend = 1
  /\ sOut \in Msg
  /\ delivered = << >>
  /\ chD = << >>
  /\ chA = << >>

\* Sender actions

SendNew ==
  /\ sCur = 0
  /\ nextToSend <= Len(ToSend)
  /\ sCur' = nextToSend
  /\ sOut' = [v |-> ToSend[nextToSend], b |-> sBit]
  /\ chD'  = Append(chD, sOut')
  /\ nextToSend' = nextToSend
  /\ UNCHANGED << sBit, rBit, delivered, chA >>

Retransmit ==
  /\ sCur # 0
  /\ chD' = Append(chD, sOut)
  /\ UNCHANGED << sBit, rBit, sCur, sOut, nextToSend, delivered, chA >>

\* Receiver consumes a data message from the unreliable data channel (arbitrary position).
\* Accepts iff incoming bit differs from rBit; always emits an acknowledgment with its current bit (after possible update).
DeliverData ==
  /\ Len(chD) > 0
  /\ \E i \in 1..Len(chD):
       LET m == chD[i]
           newChD == RemoveAt(chD, i)
           fresh == m.b # rBit
       IN /\ chD' = newChD
          /\ rBit' = IF fresh THEN m.b ELSE rBit
          /\ delivered' = IF fresh THEN Append(delivered, m.v) ELSE delivered
          /\ chA' = Append(chA, [b |-> IF fresh THEN m.b ELSE rBit])
          /\ UNCHANGED << sBit, sCur, sOut, nextToSend >>

\* Unreliable data channel may lose or duplicate messages
DropData ==
  /\ Len(chD) > 0
  /\ \E i \in 1..Len(chD): chD' = RemoveAt(chD, i)
  /\ UNCHANGED << sBit, rBit, sCur, sOut, nextToSend, delivered, chA >>

DupData ==
  /\ Len(chD) > 0
  /\ \E i \in 1..Len(chD): chD' = Append(chD, chD[i])
  /\ UNCHANGED << sBit, rBit, sCur, sOut, nextToSend, delivered, chA >>

\* Sender consumes an acknowledgment from the unreliable ack channel (arbitrary position).
\* Progress only when the ack bit matches the sender's outstanding bit.
DeliverAck ==
  /\ Len(chA) > 0
  /\ \E i \in 1..Len(chA):
       LET a == chA[i]
           newChA == RemoveAt(chA, i)
           match == (a.b = sBit) /\ (sCur # 0)
       IN /\ chA' = newChA
          /\ sBit' = IF match THEN 1 - sBit ELSE sBit
          /\ sCur' = IF match THEN 0 ELSE sCur
          /\ nextToSend' = IF match THEN nextToSend + 1 ELSE nextToSend
          /\ UNCHANGED << rBit, sOut, delivered, chD >>

\* Unreliable ack channel may lose or duplicate acks
DropAck ==
  /\ Len(chA) > 0
  /\ \E i \in 1..Len(chA): chA' = RemoveAt(chA, i)
  /\ UNCHANGED << sBit, rBit, sCur, sOut, nextToSend, delivered, chD >>

DupAck ==
  /\ Len(chA) > 0
  /\ \E i \in 1..Len(chA): chA' = Append(chA, chA[i])
  /\ UNCHANGED << sBit, rBit, sCur, sOut, nextToSend, delivered, chD >>

\* System step
Next ==
  SendNew \/ Retransmit \/
  DeliverData \/ DropData \/ DupData \/
  DeliverAck  \/ DropAck  \/ DupAck

Spec ==
  Init /\ [][Next]_vars
  /\ SF_vars(DeliverData)  \* Fair-loss for data: if data keeps arriving in the channel, some deliveries occur
  /\ SF_vars(DeliverAck)   \* Fair-loss for acks: if acks keep arriving in the channel, some deliveries occur

\* Type and basic safety properties

TypeOK ==
  /\ sBit \in Bits
  /\ rBit \in Bits
  /\ sCur \in 0..Len(ToSend)
  /\ nextToSend \in 1..(Len(ToSend) + 1)
  /\ sOut \in Msg
  /\ delivered \in Seq(DSet)
  /\ chD \in Seq(Msg)
  /\ chA \in Seq(Ack)

Prefix(p, s) == \E n \in 0..Len(s): p = SubSeq(s, 1, n)

\* Safety: delivered sequence is always a prefix of the sent sequence (no spurious deliveries, no duplication).
Safety_NoSpurious_NoDup == [] (Prefix(delivered, ToSend))

\* Agreement on sequence bits and sender state:
\* - Sender's and receiver's bits are always complementary.
\* - When there is an outstanding item, sOut reflects it.
BitsAgreementState ==
  [] ( (sCur = 0  => rBit = 1 - sBit)
    /\ (sCur # 0 => /\ rBit = 1 - sBit
                    /\ sOut.b = sBit
                    /\ sCur <= Len(ToSend)
                    /\ ToSend \in Seq(DSet)
                    /\ sOut.v = ToSend[sCur]) )

\* Acknowledgments created by the receiver carry the receiver's last-delivered bit at that moment.
AckMatchesReceiverWhenEnqueued ==
  [] ( DeliverData => chA' = Append(chA, [b |-> rBit']) )

\* Liveness: Every data item that the sender starts to send (becomes outstanding)
\* will eventually be delivered by the receiver (thus delivered grows to include it).
EventuallyDeliversAllStarted ==
  \A i \in 1..Len(ToSend): [] (sCur = i => <> (Len(delivered) >= i))

\* Collected properties
SafetyInv == TypeOK /\ Prefix(delivered, ToSend)
Liveness == EventuallyDeliversAllStarted

====