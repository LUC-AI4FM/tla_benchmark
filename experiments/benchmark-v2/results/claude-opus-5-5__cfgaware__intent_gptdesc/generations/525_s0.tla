---------------------------- MODULE ABESpec ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ConstData == {"d1", "d2"}

VARIABLES inQ,     \* environment-generated proposals awaiting the sender
          sVal,    \* latest accepted proposal value at the sender
          sBit,    \* alternating-bit tag of the latest accepted proposal
          sReady,  \* sender has received acknowledgement for current tag
          rVal,    \* value adopted by the receiver
          rBit,    \* tag of the value adopted by the receiver
          msgC,    \* sender -> receiver channel (lossy, duplicating)
          ackC,    \* receiver -> sender channel (lossy, duplicating)
          proposed \* history: set of all values ever proposed

vars == <<inQ, sVal, sBit, sReady, rVal, rBit, msgC, ackC, proposed>>

Bits == {0, 1}

Remove(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------

ABESpec_TypeOK ==
  /\ inQ \in Seq(Data)
  /\ sVal \in Data
  /\ sBit \in Bits
  /\ sReady \in BOOLEAN
  /\ rVal \in Data
  /\ rBit \in Bits
  /\ msgC \in Seq(Bits \X Data)
  /\ ackC \in Seq(Bits)
  /\ proposed \subseteq Data

StateConstraint ==
  /\ Len(inQ) <= 2
  /\ Len(msgC) <= 3
  /\ Len(ackC) <= 3

-----------------------------------------------------------------------------

Init ==
  \E d \in Data :
    /\ inQ = << >>
    /\ sVal = d
    /\ sBit = 0
    /\ sReady = TRUE
    /\ rVal = d
    /\ rBit = 0
    /\ msgC = << >>
    /\ ackC = << >>
    /\ proposed = {d}

\* Environment produces a new proposal (may happen at any time)
Propose(d) ==
  /\ inQ' = Append(inQ, d)
  /\ proposed' = proposed \cup {d}
  /\ UNCHANGED <<sVal, sBit, sReady, rVal, rBit, msgC, ackC>>

\* Sender accepts the next proposal once the previous one is acknowledged
SndNew ==
  /\ sReady
  /\ inQ # << >>
  /\ sVal' = Head(inQ)
  /\ sBit' = 1 - sBit
  /\ sReady' = FALSE
  /\ inQ' = Tail(inQ)
  /\ UNCHANGED <<rVal, rBit, msgC, ackC, proposed>>

\* Sender (re)transmits the latest accepted proposal and its tag
SndMsg ==
  /\ msgC' = Append(msgC, <<sBit, sVal>>)
  /\ UNCHANGED <<inQ, sVal, sBit, sReady, rVal, rBit, ackC, proposed>>

\* Receiver consumes a message; adopts it only if the tag is new
RcvMsg ==
  /\ msgC # << >>
  /\ LET m == Head(msgC) IN
       /\ msgC' = Tail(msgC)
       /\ IF m[1] # rBit
            THEN /\ rBit' = m[1]
                 /\ rVal' = m[2]
            ELSE UNCHANGED <<rBit, rVal>>
  /\ UNCHANGED <<inQ, sVal, sBit, sReady, ackC, proposed>>

\* Receiver (re)transmits acknowledgement of its current tag
SndAck ==
  /\ ackC' = Append(ackC, rBit)
  /\ UNCHANGED <<inQ, sVal, sBit, sReady, rVal, rBit, msgC, proposed>>

\* Sender consumes an acknowledgement
RcvAck ==
  /\ ackC # << >>
  /\ ackC' = Tail(ackC)
  /\ sReady' = (sReady \/ Head(ackC) = sBit)
  /\ UNCHANGED <<inQ, sVal, sBit, rVal, rBit, msgC, proposed>>

\* Channels may lose messages
LoseMsg ==
  /\ \E i \in 1..Len(msgC) : msgC' = Remove(msgC, i)
  /\ UNCHANGED <<inQ, sVal, sBit, sReady, rVal, rBit, ackC, proposed>>

LoseAck ==
  /\ \E i \in 1..Len(ackC) : ackC' = Remove(ackC, i)
  /\ UNCHANGED <<inQ, sVal, sBit, sReady, rVal, rBit, msgC, proposed>>

Next ==
  \/ \E d \in Data : Propose(d)
  \/ SndNew
  \/ SndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

Fairness ==
  /\ WF_vars(SndNew)
  /\ WF_vars(SndMsg)
  /\ WF_vars(SndAck)
  /\ SF_vars(RcvMsg)
  /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

TagAgreement == (rBit = sBit) => (rVal = sVal)

ValidDelivery == rVal \in proposed /\ sVal \in proposed

Safety == ABESpec_TypeOK /\ TagAgreement /\ ValidDelivery

\* Liveness properties

\* Every accepted proposal is eventually adopted or superseded by a later one
AcceptedEventuallyResolved ==
  \A b \in Bits, d \in Data :
    [](((sBit = b) /\ (sVal = d)) =>
        <>((rBit = b /\ rVal = d) \/ (sBit # b)))

\* If proposals stop arriving, receiver catches up with sender infinitely often
EventuallyEqual ==
  (<>[](inQ = << >>)) => []<>(rBit = sBit /\ rVal = sVal)

Liveness == AcceptedEventuallyResolved /\ EventuallyEqual

THEOREM Spec => [](ABESpec_TypeOK /\ TagAgreement /\ ValidDelivery)
=============================================================================