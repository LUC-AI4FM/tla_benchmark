------------------------------ MODULE AlternatingBitProtocol ------------------------------
(***************************************************************************)
(* Alternating-bit protocol over lossy FIFO channels.                      *)
(*                                                                         *)
(* A sender holds a local outbound queue of application data and a current *)
(* candidate tagged with a one-bit sequence number. It repeatedly sends    *)
(* <<bit, candidate>> on a lossy FIFO data channel. The receiver reads     *)
(* messages in order. A message whose bit differs from the receiver's last *)
(* accepted bit is accepted: the receiver stores the data and records the  *)
(* bit. The receiver repeatedly sends acknowledgments carrying its last    *)
(* accepted bit on a lossy FIFO ack channel. When the sender receives an   *)
(* ack equal to its current bit, it flips its bit and installs the next    *)
(* queued item as the new candidate.                                       *)
(*                                                                         *)
(* Channels may drop any message, but the remaining messages keep their    *)
(* order. The environment may append new data to the sender's queue        *)
(* whenever the sender and receiver bits agree.                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Data,       \* set of application data values
    MaxItems,   \* bound on total number of generated items (for finiteness)
    MaxChan     \* bound on the number of messages in each channel

ASSUME /\ Data # {}
       /\ MaxItems \in Nat
       /\ MaxChan \in Nat \ {0}

NoData == CHOOSE v : v \notin Data      \* placeholder before any data exists

Bits == {0, 1}
Flip(b) == 1 - b

Range(s) == { s[i] : i \in DOMAIN s }

\* Remove the i-th element of s, preserving the order of the others.
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* s is an order-preserving subsequence of t.
IsSubSeqOf(s, t) ==
    \E f \in [1..Len(s) -> 1..Len(t)] :
        /\ \A i, j \in 1..Len(s) : i < j => f[i] < f[j]
        /\ \A i \in 1..Len(s) : s[i] = t[f[i]]

VARIABLES
    sBit,       \* sender's one-bit sequence state
    sData,      \* sender's current candidate for transmission
    sQueue,     \* sender's local outbound queue
    sCount,     \* number of advancements made by the sender (ghost)
    rBit,       \* receiver's last accepted bit
    rData,      \* receiver's stored (last accepted) data
    msgQ,       \* sender -> receiver channel: sequence of <<bit, data>>
    ackQ,       \* receiver -> sender channel: sequence of bits
    gen,        \* history of all generated data, in order (ghost)
    delivered   \* history of all data accepted by receiver, in order (ghost)

vars == << sBit, sData, sQueue, sCount, rBit, rData, msgQ, ackQ, gen, delivered >>

Messages == Bits \X (Data \cup {NoData})

TypeOK ==
    /\ sBit \in Bits
    /\ rBit \in Bits
    /\ sData \in Data \cup {NoData}
    /\ rData \in Data \cup {NoData}
    /\ sQueue \in Seq(Data)
    /\ sCount \in Nat
    /\ msgQ \in Seq(Messages)
    /\ ackQ \in Seq(Bits)
    /\ gen \in Seq(Data)
    /\ delivered \in Seq(Data)

---------------------------------------------------------------------------
Init ==
    /\ sBit = 0
    /\ rBit = 0
    /\ sData = NoData
    /\ rData = NoData
    /\ sQueue = << >>
    /\ sCount = 0
    /\ msgQ = << >>
    /\ ackQ = << >>
    /\ gen = << >>
    /\ delivered = << >>

\* Environment: append a new application data item when sender and receiver agree.
Enqueue(d) ==
    /\ sBit = rBit
    /\ Len(gen) < MaxItems
    /\ sQueue' = Append(sQueue, d)
    /\ gen' = Append(gen, d)
    /\ UNCHANGED << sBit, sData, sCount, rBit, rData, msgQ, ackQ, delivered >>

\* Sender (re)transmits its current candidate with its current bit.
SndMsg ==
    /\ Len(msgQ) < MaxChan
    /\ msgQ' = Append(msgQ, << sBit, sData >>)
    /\ UNCHANGED << sBit, sData, sQueue, sCount, rBit, rData, ackQ, gen, delivered >>

\* Sender reads an acknowledgment. If it matches the current bit and there is
\* a next item, the sender advances: flips the bit and installs the next item.
RcvAck ==
    /\ ackQ # << >>
    /\ ackQ' = Tail(ackQ)
    /\ IF Head(ackQ) = sBit /\ sQueue # << >>
          THEN /\ sBit' = Flip(sBit)
               /\ sData' = Head(sQueue)
               /\ sQueue' = Tail(sQueue)
               /\ sCount' = sCount + 1
          ELSE UNCHANGED << sBit, sData, sQueue, sCount >>
    /\ UNCHANGED << rBit, rData, msgQ, gen, delivered >>

\* Receiver reads the head message; accepts it iff its bit differs from rBit.
RcvMsg ==
    /\ msgQ # << >>
    /\ msgQ' = Tail(msgQ)
    /\ LET m == Head(msgQ) IN
         IF m[1] # rBit
            THEN /\ rBit' = m[1]
                 /\ rData' = m[2]
                 /\ delivered' = Append(delivered, m[2])
            ELSE UNCHANGED << rBit, rData, delivered >>
    /\ UNCHANGED << sBit, sData, sQueue, sCount, ackQ, gen >>

\* Receiver (re)sends an acknowledgment carrying its last accepted bit.
SndAck ==
    /\ Len(ackQ) < MaxChan
    /\ ackQ' = Append(ackQ, rBit)
    /\ UNCHANGED << sBit, sData, sQueue, sCount, rBit, rData, msgQ, gen, delivered >>

\* Lossy channels: any single message may be dropped; order of rest preserved.
LoseMsg ==
    /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
    /\ UNCHANGED << sBit, sData, sQueue, sCount, rBit, rData, ackQ, gen, delivered >>

LoseAck ==
    /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
    /\ UNCHANGED << sBit, sData, sQueue, sCount, rBit, rData, msgQ, gen, delivered >>

Next ==
    \/ \E d \in Data : Enqueue(d)
    \/ SndMsg
    \/ RcvAck
    \/ RcvMsg
    \/ SndAck
    \/ LoseMsg
    \/ LoseAck

\* Fair scheduling: sender and receiver keep taking their steps. Strong
\* fairness on receives ensures that, despite arbitrary losses, messages
\* are received infinitely often if they are infinitely often available.
Fairness ==
    /\ SF_vars(SndMsg)
    /\ SF_vars(RcvMsg)
    /\ SF_vars(SndAck)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Invariants *)

\* Data previously installed at the sender, before the current candidate.
PrevData == IF sCount <= 1 THEN NoData ELSE gen[sCount - 1]

\* Sequence bits: start equal; each flips exactly with an advancement.
BitInvariant ==
    /\ sBit = sCount % 2
    /\ rBit = Len(delivered) % 2
    /\ \/ Len(delivered) = sCount
       \/ Len(delivered) + 1 = sCount

\* The sender's queue is exactly the not-yet-installed generated items.
SenderQueueInvariant ==
    /\ sCount <= Len(gen)
    /\ sQueue = SubSeq(gen, sCount + 1, Len(gen))
    /\ sData = IF sCount = 0 THEN NoData ELSE gen[sCount]

\* Receiver's stored data equals the data sent with its current bit.
ReceiverDataInvariant ==
    /\ rData = IF Len(delivered) = 0 THEN NoData ELSE gen[Len(delivered)]
    /\ rBit = sBit => rData = sData
    /\ rBit # sBit => rData = PrevData

\* Safety: accepted data are delivered in order, without duplication or gaps.
InOrderDelivery ==
    /\ Len(delivered) <= Len(gen)
    /\ delivered = SubSeq(gen, 1, Len(delivered))

\* Safety: accepted data come from the sender's generated data set.
DeliveredFromGenerated ==
    /\ Range(delivered) \subseteq Range(gen)
    /\ rData \in Range(gen) \cup {NoData}

\* Messages in transit carry either the current candidate or the previous one.
ChannelContentInvariant ==
    /\ \A i \in 1..Len(msgQ) :
          \/ msgQ[i] = << sBit, sData >>
          \/ msgQ[i] = << Flip(sBit), PrevData >>
    /\ \A i \in 1..Len(ackQ) : ackQ[i] \in Bits

Inv ==
    /\ TypeOK
    /\ BitInvariant
    /\ SenderQueueInvariant
    /\ ReceiverDataInvariant
    /\ InOrderDelivery
    /\ DeliveredFromGenerated
    /\ ChannelContentInvariant

---------------------------------------------------------------------------
(* Action (step) properties *)

\* Bits flip only on successful advancement.
BitsFlipOnlyOnAdvance ==
    /\ [][sBit' # sBit => sCount' = sCount + 1]_vars
    /\ [][rBit' # rBit => Len(delivered') = Len(delivered) + 1]_vars

\* No duplicate acceptance without an intervening sender advancement:
\* each acceptance adds exactly one item and corresponds to the latest
\* sender advancement.
NoDuplicateAcceptance ==
    [][Len(delivered') # Len(delivered) =>
          /\ Len(delivered') = Len(delivered) + 1
          /\ Len(delivered') = sCount
          /\ delivered' = Append(delivered, gen[sCount])]_vars

\* Channel property: losses may remove messages but never reorder them.
ChannelOrderPreserved ==
    /\ [][Len(msgQ') <= Len(msgQ) => IsSubSeqOf(msgQ', msgQ)]_msgQ
    /\ [][Len(msgQ') > Len(msgQ) => msgQ = SubSeq(msgQ', 1, Len(msgQ))]_msgQ
    /\ [][Len(ackQ') <= Len(ackQ) => IsSubSeqOf(ackQ', ackQ)]_ackQ
    /\ [][Len(ackQ') > Len(ackQ) => ackQ = SubSeq(ackQ', 1, Len(ackQ))]_ackQ

---------------------------------------------------------------------------
(* Liveness *)

\* Every enqueued data item is eventually accepted by the receiver.
EventualDelivery ==
    \A i \in 1..MaxItems : (Len(gen) >= i) ~> (Len(delivered) >= i)

\* Sender and receiver always eventually come back into agreement.
EventualAgreement == []<>(sBit = rBit)

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => BitsFlipOnlyOnAdvance /\ NoDuplicateAcceptance /\ ChannelOrderPreserved
THEOREM Spec => EventualDelivery /\ EventualAgreement
===========================================================================================