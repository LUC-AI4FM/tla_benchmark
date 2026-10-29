------------------------------- MODULE AlternatingBit -------------------------------
(***************************************************************************)
(* Alternating Bit Protocol over two unbounded, lossy, FIFO channels.      *)
(*                                                                         *)
(* The sender transmits the items of the sequence Input one at a time.     *)
(* Each data message carries a one-bit sequence number. The sender         *)
(* retransmits the current item until it receives an acknowledgement      *)
(* carrying the same bit, and then advances to the next item.              *)
(*                                                                         *)
(* The receiver accepts a message only when its bit equals the expected    *)
(* bit. It acknowledges by returning the bit of the last item it accepted. *)
(*                                                                         *)
(* The network may drop any queued message at any time. It never reorders, *)
(* duplicates, or corrupts messages.                                       *)
(*                                                                         *)
(* Ghost variables sentMsgs, acksSent and delivLog are history variables.  *)
(* They exist only so that the correctness properties can be stated.       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Data,       \* set of possible data values
    Input,      \* the sequence of data items the sender must transmit
    MaxQueue    \* bound used ONLY by the TLC state constraint below (not by Spec)

ASSUME InputOK    == Input \in Seq(Data)
ASSUME MaxQueueOK == MaxQueue \in Nat

Bits     == {0, 1}
Flip(b)  == 1 - b
Msgs     == [bit : Bits, data : Data]

\* Remove the i-th element of sequence s.
Remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

VARIABLES
    sIdx,      \* index into Input of the item the sender is currently sending
    sBit,      \* sender's current sequence bit
    rBit,      \* bit the receiver expects next
    msgQ,      \* sender -> receiver channel (FIFO sequence of Msgs)
    ackQ,      \* receiver -> sender channel (FIFO sequence of Bits)
    output,    \* data items delivered by the receiver, in delivery order
    sentMsgs,  \* ghost: set of every data message ever put on msgQ
    acksSent,  \* ghost: set of every ack bit ever put on ackQ
    delivLog   \* ghost: sequence of the messages (bit and data) the receiver accepted

vars == << sIdx, sBit, rBit, msgQ, ackQ, output, sentMsgs, acksSent, delivLog >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ sIdx \in 1..(Len(Input) + 1)
    /\ sBit \in Bits
    /\ rBit \in Bits
    /\ msgQ \in Seq(Msgs)
    /\ ackQ \in Seq(Bits)
    /\ output \in Seq(Data)
    /\ sentMsgs \subseteq Msgs
    /\ acksSent \subseteq Bits
    /\ delivLog \in Seq(Msgs)

Init ==
    /\ sIdx = 1
    /\ sBit = 0
    /\ rBit = 0
    /\ msgQ = << >>
    /\ ackQ = << >>
    /\ output = << >>
    /\ sentMsgs = {}
    /\ acksSent = {}
    /\ delivLog = << >>

-----------------------------------------------------------------------------
(* Sender actions *)

\* Send, or retransmit, the current item tagged with the current bit.
SendMsg ==
    /\ sIdx <= Len(Input)
    /\ LET m == [bit |-> sBit, data |-> Input[sIdx]]
       IN  /\ msgQ' = Append(msgQ, m)
           /\ sentMsgs' = sentMsgs \cup {m}
    /\ UNCHANGED << sIdx, sBit, rBit, ackQ, output, acksSent, delivLog >>

\* Receive an ack. If it matches the current bit, advance to the next item.
\* Otherwise the ack is stale and is discarded.
RcvAck ==
    /\ ackQ # << >>
    /\ ackQ' = Tail(ackQ)
    /\ IF Head(ackQ) = sBit /\ sIdx <= Len(Input)
          THEN /\ sIdx' = sIdx + 1
               /\ sBit' = Flip(sBit)
          ELSE UNCHANGED << sIdx, sBit >>
    /\ UNCHANGED << rBit, msgQ, output, sentMsgs, acksSent, delivLog >>

-----------------------------------------------------------------------------
(* Receiver actions *)

\* Receive a data message. Accept it only if it carries the expected bit.
\* Otherwise it is a duplicate and is discarded.
RcvMsg ==
    /\ msgQ # << >>
    /\ LET m == Head(msgQ)
       IN  /\ msgQ' = Tail(msgQ)
           /\ IF m.bit = rBit
                 THEN /\ output'   = Append(output, m.data)
                      /\ delivLog' = Append(delivLog, m)
                      /\ rBit'     = Flip(rBit)
                 ELSE UNCHANGED << output, delivLog, rBit >>
    /\ UNCHANGED << sIdx, sBit, ackQ, sentMsgs, acksSent >>

\* (Re)send an ack carrying the bit of the most recently accepted message.
SendAck ==
    /\ ackQ' = Append(ackQ, Flip(rBit))
    /\ acksSent' = acksSent \cup {Flip(rBit)}
    /\ UNCHANGED << sIdx, sBit, rBit, msgQ, output, sentMsgs, delivLog >>

-----------------------------------------------------------------------------
(* Unreliable network: any queued message may be lost *)

LoseMsg ==
    /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(msgQ, i)
    /\ UNCHANGED << sIdx, sBit, rBit, ackQ, output, sentMsgs, acksSent, delivLog >>

LoseAck ==
    /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(ackQ, i)
    /\ UNCHANGED << sIdx, sBit, rBit, msgQ, output, sentMsgs, acksSent, delivLog >>

-----------------------------------------------------------------------------

Next ==
    \/ SendMsg
    \/ RcvAck
    \/ RcvMsg
    \/ SendAck
    \/ LoseMsg
    \/ LoseAck

\* Optional fairness, used only for the liveness properties.
\* The sender and receiver keep retransmitting (weak fairness).
\* Receive actions are strongly fair. This models a network that cannot
\* drop every copy forever: a channel that is nonempty infinitely often
\* eventually delivers. Message loss itself is never forced.
Fairness ==
    /\ WF_vars(SendMsg)
    /\ WF_vars(SendAck)
    /\ SF_vars(RcvMsg)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety-only specification with no fairness assumptions.
SafetySpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

IsPrefix(s, t) == Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))

\* No duplicates and no reordering. The delivered sequence is always exactly
\* the first Len(output) items of Input. Each item is delivered at most once,
\* and items arrive in their original order.
InOrderNoDup == IsPrefix(output, Input)

\* Consistency. Every delivered value was actually transmitted by the sender,
\* and the k-th delivery is the k-th input item.
DeliveredWasSent ==
    \A k \in 1..Len(delivLog) :
        /\ delivLog[k] \in sentMsgs
        /\ delivLog[k].data = Input[k]

\* Agreement between bits and messages. The k-th item is delivered with bit
\* (k-1) % 2, which is exactly the bit the sender used for it.
DeliveredBitMatches ==
    /\ Len(delivLog) = Len(output)
    /\ \A k \in 1..Len(delivLog) :
          /\ delivLog[k].bit  = (k - 1) % 2
          /\ delivLog[k].data = output[k]

\* Sender and receiver bits track their positions in the sequence.
BitsConsistent ==
    /\ sBit = (sIdx - 1) % 2
    /\ rBit = Len(output) % 2
    /\ Len(output) \in {sIdx - 1, sIdx}
    /\ (rBit = sBit) <=> (Len(output) = sIdx - 1)

\* The sender advances only after the current item has been delivered.
SenderAdvancesOnlyAfterDelivery == sIdx - 1 <= Len(output)

\* Acks correspond to messages that were actually accepted. An ack carrying
\* the sender's current bit exists only if the current item was delivered.
AckCorrespondence ==
    \A i \in 1..Len(ackQ) :
        ackQ[i] = sBit => Len(output) = sIdx

\* No silent corruption. Every in-flight message is one the sender actually
\* sent, with an unchanged bit and payload. In-flight data is always the
\* current item (current bit) or the previous item (previous bit).
NoCorruption ==
    /\ \A i \in 1..Len(msgQ) : msgQ[i] \in sentMsgs
    /\ \A i \in 1..Len(ackQ) : ackQ[i] \in acksSent
    /\ \A i \in 1..Len(msgQ) :
          IF msgQ[i].bit = sBit
             THEN /\ sIdx <= Len(Input)
                  /\ msgQ[i].data = Input[sIdx]
             ELSE /\ sIdx > 1
                  /\ msgQ[i].data = Input[sIdx - 1]
                  /\ Len(output) = sIdx - 1

Safety ==
    /\ TypeOK
    /\ InOrderNoDup
    /\ DeliveredWasSent
    /\ DeliveredBitMatches
    /\ BitsConsistent
    /\ SenderAdvancesOnlyAfterDelivery
    /\ AckCorrespondence
    /\ NoCorruption

\* Action property: output only ever grows by appending the next input item.
OutputGrowsInOrder ==
    [][ \/ output' = output
        \/ /\ Len(output) < Len(Input)
           /\ output' = Append(output, Input[Len(output) + 1]) ]_vars

\* Action property: the sender advances by exactly one item at a time, and
\* only if the item it is leaving has been delivered.
SenderStepsByOne ==
    [][ sIdx' # sIdx => (sIdx' = sIdx + 1 /\ Len(output) >= sIdx) ]_vars

-----------------------------------------------------------------------------
(* Liveness properties (optional; these hold under Spec's fairness) *)

\* Every input item is eventually delivered.
EventualDelivery == <>(output = Input)

\* The sender eventually progresses past every item.
SenderProgress ==
    \A k \in 1..Len(Input) : <>(sIdx > k)

\* The sender eventually finishes the whole input.
SenderCompletes == <>(sIdx = Len(Input) + 1)

-----------------------------------------------------------------------------
(* TLC state constraint, used only for finite model checking. It bounds    *)
(* the otherwise unbounded queues. It is not part of the specification.    *)
QueueConstraint ==
    /\ Len(msgQ) <= MaxQueue
    /\ Len(ackQ) <= MaxQueue

THEOREM Spec => []Safety
THEOREM Spec => OutputGrowsInOrder /\ SenderStepsByOne
THEOREM Spec => EventualDelivery /\ SenderProgress /\ SenderCompletes
==============================================================================