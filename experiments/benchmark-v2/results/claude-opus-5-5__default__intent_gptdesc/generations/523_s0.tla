---------------------------- MODULE ABProposal ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Values,        \* set of values that may be proposed
          BufMax,        \* bound on the proposer's input buffer
          ChanMax,       \* bound on each channel's length
          MaxProposals   \* bound on total environment proposals (finiteness)

ASSUME /\ Values # {}
       /\ BufMax \in Nat \ {0}
       /\ ChanMax \in Nat \ {0}
       /\ MaxProposals \in Nat

NoVal == CHOOSE v : v \notin Values
Bits  == {0, 1}
Msgs  == [bit : Bits, val : Values]

VARIABLES pBit,       \* proposer's current alternating bit
          pAck,       \* last ack bit received by the proposer
          pVal,       \* proposer's current (outstanding or last) value
          buf,        \* proposer's bounded buffer of pending proposals
          msgQ,       \* forward FIFO channel proposer -> acceptor
          ackQ,       \* backward FIFO channel acceptor -> proposer
          aBit,       \* acceptor's last accepted bit
          aVal,       \* acceptor's last delivered value
          hist,       \* history: proposals taken up by the proposer (bit, val)
          delivered,  \* history: values delivered to the acceptor's application
          nProposed   \* number of proposals injected by the environment

vars == <<pBit, pAck, pVal, buf, msgQ, ackQ, aBit, aVal,
          hist, delivered, nProposed>>

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

-----------------------------------------------------------------------------
Init ==
  /\ pBit = 0
  /\ pAck = 0
  /\ pVal = NoVal
  /\ buf = << >>
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ aBit = 0
  /\ aVal = NoVal
  /\ hist = << >>
  /\ delivered = << >>
  /\ nProposed = 0

\* Environment injects a new proposal, limited by the buffer bound.
Propose(v) ==
  /\ nProposed < MaxProposals
  /\ Len(buf) < BufMax
  /\ buf' = Append(buf, v)
  /\ nProposed' = nProposed + 1
  /\ UNCHANGED <<pBit, pAck, pVal, msgQ, ackQ, aBit, aVal, hist, delivered>>

\* Proposer is idle (current proposal acknowledged) and takes the next value.
Pickup ==
  /\ pAck = pBit
  /\ buf # << >>
  /\ pBit' = 1 - pBit
  /\ pVal' = Head(buf)
  /\ buf' = Tail(buf)
  /\ hist' = Append(hist, [bit |-> 1 - pBit, val |-> Head(buf)])
  /\ UNCHANGED <<pAck, msgQ, ackQ, aBit, aVal, delivered, nProposed>>

\* Proposer (re)transmits its outstanding proposal.
SendMsg ==
  /\ pAck # pBit
  /\ Len(msgQ) < ChanMax
  /\ msgQ' = Append(msgQ, [bit |-> pBit, val |-> pVal])
  /\ UNCHANGED <<pBit, pAck, pVal, buf, ackQ, aBit, aVal,
                 hist, delivered, nProposed>>

\* Acceptor receives the head message; accepts only if the bit is new.
RcvMsg ==
  /\ msgQ # << >>
  /\ LET m == Head(msgQ) IN
       /\ msgQ' = Tail(msgQ)
       /\ IF m.bit # aBit
            THEN /\ aBit' = m.bit
                 /\ aVal' = m.val
                 /\ delivered' = Append(delivered, m)
            ELSE UNCHANGED <<aBit, aVal, delivered>>
  /\ UNCHANGED <<pBit, pAck, pVal, buf, ackQ, hist, nProposed>>

\* Acceptor acknowledges with the bit it believes current.
SendAck ==
  /\ Len(ackQ) < ChanMax
  /\ ackQ' = Append(ackQ, aBit)
  /\ UNCHANGED <<pBit, pAck, pVal, buf, msgQ, aBit, aVal,
                 hist, delivered, nProposed>>

\* Proposer receives the head acknowledgment.
RcvAck ==
  /\ ackQ # << >>
  /\ pAck' = Head(ackQ)
  /\ ackQ' = Tail(ackQ)
  /\ UNCHANGED <<pBit, pVal, buf, msgQ, aBit, aVal,
                 hist, delivered, nProposed>>

\* Channels may drop messages (order of survivors is preserved: FIFO).
LoseMsg ==
  /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
  /\ UNCHANGED <<pBit, pAck, pVal, buf, ackQ, aBit, aVal,
                 hist, delivered, nProposed>>

LoseAck ==
  /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
  /\ UNCHANGED <<pBit, pAck, pVal, buf, msgQ, aBit, aVal,
                 hist, delivered, nProposed>>

Next ==
  \/ \E v \in Values : Propose(v)
  \/ Pickup
  \/ SendMsg
  \/ RcvMsg
  \/ SendAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

\* Fairness: sends and receives that are repeatedly possible eventually occur,
\* so repeated retransmission eventually gets through despite losses.
Fairness ==
  /\ WF_vars(Pickup)
  /\ SF_vars(SendMsg)
  /\ SF_vars(RcvMsg)
  /\ SF_vars(SendAck)
  /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Type invariant
TypeOK ==
  /\ pBit \in Bits
  /\ pAck \in Bits
  /\ pVal \in Values \cup {NoVal}
  /\ buf \in Seq(Values)
  /\ msgQ \in Seq(Msgs)
  /\ ackQ \in Seq(Bits)
  /\ aBit \in Bits
  /\ aVal \in Values \cup {NoVal}
  /\ hist \in Seq(Msgs)
  /\ delivered \in Seq(Msgs)
  /\ nProposed \in 0..MaxProposals

\* Channel and buffer length bounds
BoundsOK ==
  /\ Len(msgQ) <= ChanMax
  /\ Len(ackQ) <= ChanMax
  /\ Len(buf) <= BufMax

ProposedVals ==
  {hist[i].val : i \in 1..Len(hist)} \cup {buf[i] : i \in 1..Len(buf)}

\* Safety: every delivered value was actually proposed, deliveries are exactly
\* the proposals in order (non-corrupting, no reordering), consecutive
\* deliveries alternate bits, so no two different values for the same round.
Safety ==
  /\ \A i \in 1..Len(delivered) : delivered[i].val \in ProposedVals
  /\ Len(delivered) <= Len(hist)
  /\ delivered = SubSeq(hist, 1, Len(delivered))
  /\ Len(hist) - Len(delivered) \in {0, 1}
  /\ \A i \in 1..(Len(delivered) - 1) : delivered[i].bit # delivered[i+1].bit

\* No two different values ever delivered under the same bit within a round:
\* any message in transit carrying the proposer's current bit carries pVal.
ConsistentChannel ==
  \A i \in 1..Len(msgQ) : msgQ[i].bit = pBit => msgQ[i].val = pVal

\* No spurious acceptance
NoSpuriousAcceptance ==
  (aBit = pBit) => (pVal = aVal)

\* "Two-values" pattern: each channel consists of a block of copies of one
\* value followed by a block of copies of another (at most one change point).
TwoValues(q) ==
  \A i, j \in 1..(Len(q) - 1) :
     (q[i] # q[i+1] /\ q[j] # q[j+1]) => i = j

TwoValuesInv ==
  /\ TwoValues(msgQ)
  /\ TwoValues(ackQ)

Inv ==
  /\ TypeOK
  /\ BoundsOK
  /\ Safety
  /\ ConsistentChannel
  /\ NoSpuriousAcceptance
  /\ TwoValuesInv

-----------------------------------------------------------------------------
\* Liveness: every value taken up by the proposer is eventually accepted.
\* (Since nothing is discarded, a proposal is accepted before being
\* superseded by the next one.)
EveryProposalAccepted ==
  \A k \in 1..MaxProposals : (Len(hist) >= k) ~> (Len(delivered) >= k)

\* Every buffered proposal is eventually taken up and accepted.
BufferDrains ==
  \A v \in Values : (\E i \in 1..Len(buf) : buf[i] = v) ~>
                    (\E i \in 1..Len(delivered) : delivered[i].val = v)

\* Outstanding current proposal is eventually accepted and acknowledged.
CurrentEventuallyAcked ==
  (pAck # pBit) ~> (pAck = pBit /\ aBit = pBit /\ aVal = pVal)

\* When the proposer stops receiving new proposals, its current proposal is
\* eventually accepted and acknowledged, and stays so.
QuiescenceAccepted ==
  (<>[](buf = << >>)) => <>[](pAck = pBit /\ aBit = pBit /\ aVal = pVal)

Liveness ==
  /\ EveryProposalAccepted
  /\ BufferDrains
  /\ CurrentEventuallyAcked
  /\ QuiescenceAccepted

THEOREM Spec => []Inv
THEOREM Spec => Liveness
=============================================================================