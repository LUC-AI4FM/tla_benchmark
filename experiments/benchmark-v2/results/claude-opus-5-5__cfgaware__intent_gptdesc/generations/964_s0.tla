------------------------------ MODULE AlternatingBit ------------------------------
(***************************************************************************)
(* Alternating Bit protocol: one sender, one receiver, and two lossy FIFO  *)
(* channels. msgQ carries <<bit, data>> packets from sender to receiver.  *)
(* ackQ carries bits from receiver to sender. Either channel may lose     *)
(* individual messages. It never duplicates, reorders or corrupts them.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ,   \* data channel: sequence of <<bit, datum>>
          ackQ,   \* ack channel: sequence of bits
          sBit,   \* sender's current sequence bit
          sAck,   \* last ack bit received by sender
          rBit,   \* receiver's last accepted bit (expects 1 - rBit next)
          sent,   \* datum currently being sent
          rcvd    \* last datum delivered to the receiver's application

vars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd >>

Bits == {0, 1}

-----------------------------------------------------------------------------
ABTypeInv ==
  /\ msgQ \in Seq(Bits \X Data)
  /\ ackQ \in Seq(Bits)
  /\ sBit \in Bits
  /\ sAck \in Bits
  /\ rBit \in Bits
  /\ sent \in Data
  /\ rcvd \in Data

ABInit ==
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ sBit \in Bits
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd = sent

-----------------------------------------------------------------------------
(* The sender accepts a new datum once the previous packet is acknowledged. *)
SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, << 1 - sBit, d >>)
  /\ UNCHANGED << ackQ, sAck, rBit, rcvd >>

(* The sender suspects loss and retransmits the last packet. *)
ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, << sBit, sent >>)
  /\ UNCHANGED << ackQ, sBit, sAck, rBit, sent, rcvd >>

(* The receiver takes a packet. It delivers the datum only when the bit   *)
(* matches the expected bit (1 - rBit), then toggles its expected bit.    *)
(* Duplicates are discarded.                                              *)
RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ IF Head(msgQ)[1] # rBit
       THEN /\ rBit' = Head(msgQ)[1]
            /\ rcvd' = Head(msgQ)[2]
       ELSE UNCHANGED << rBit, rcvd >>
  /\ UNCHANGED << ackQ, sBit, sAck, sent >>

(* The receiver acknowledges the last bit it accepted. *)
SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED << msgQ, sBit, sAck, rBit, sent, rcvd >>

(* The sender receives an acknowledgment. *)
RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED << msgQ, sBit, rBit, sent, rcvd >>

(* Remove the i-th element of a sequence. *)
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

LoseMsg ==
  /\ msgQ # << >>
  /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
  /\ UNCHANGED << ackQ, sBit, sAck, rBit, sent, rcvd >>

LoseAck ==
  /\ ackQ # << >>
  /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
  /\ UNCHANGED << msgQ, sBit, sAck, rBit, sent, rcvd >>

ABNext ==
  \/ \E d \in Data : SndNewValue(d)
  \/ ReSndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

-----------------------------------------------------------------------------
ABFairness ==
  /\ WF_vars(ReSndMsg)
  /\ WF_vars(SndAck)
  /\ SF_vars(RcvMsg)
  /\ SF_vars(RcvAck)

ABSpec == ABInit /\ [][ABNext]_vars /\ ABFairness

-----------------------------------------------------------------------------
(* Safety: every packet carrying the sender's current bit carries the     *)
(* current datum. When the receiver has accepted the current bit, it      *)
(* holds exactly the datum the sender sent, so data is never corrupted.   *)
DataIntegrity ==
  /\ \A i \in 1..Len(msgQ) : msgQ[i][1] = sBit => msgQ[i][2] = sent
  /\ rBit = sBit => rcvd = sent

(* Safety: when the sender holds an acknowledgment for the current bit,   *)
(* the receiver has accepted it. Because delivery requires a bit change,  *)
(* each datum is delivered at most once.                                  *)
AckSound == (sAck = sBit) => (rBit = sBit)

ABInvariant == ABTypeInv /\ DataIntegrity /\ AckSound

(* Liveness: every datum the sender transmits is eventually delivered and *)
(* eventually acknowledged.                                               *)
EventuallyDelivered ==
  \A b \in Bits : (sBit = b /\ rBit # b) ~> (rBit = b)

EventuallyAcked ==
  \A b \in Bits : (sBit = b /\ sAck # b) ~> (sAck = b)

ABLiveness == EventuallyDelivered /\ EventuallyAcked

THEOREM ABSpec => []ABTypeInv
THEOREM ABSpec => []ABInvariant
THEOREM ABSpec => ABLiveness
=============================================================================