------------------------------ MODULE AlternatingBitProposals ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Values,         \* the set of values the environment may propose
    QLen,           \* bound on the environment proposal queue
    MaxProposals,   \* bound on the total number of proposals the environment produces
    MaxChan         \* bound on the length of each channel (keeps the model finite)

ASSUME
    /\ Values # {}
    /\ QLen \in Nat \ {0}
    /\ MaxProposals \in Nat
    /\ MaxChan \in Nat \ {0}

VARIABLES
    envQ,       \* bounded queue of externally generated proposals
    count,      \* number of proposals generated so far
    proposed,   \* set of every value ever proposed (history variable)
    sVal,       \* sender's latest accepted value
    sBit,       \* sender's alternating-bit tag
    sAcked,     \* sender knows the receiver adopted (sVal, sBit)
    rVal,       \* receiver's adopted value
    rBit,       \* receiver's tag of the adopted value
    msgQ,       \* data channel, sender -> receiver
    ackQ        \* acknowledgment channel, receiver -> sender

vars == <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, msgQ, ackQ>>

Bits == {0, 1}
Msgs == Values \X Bits

Flip(b) == 1 - b

Remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
Dup(s, i)    == SubSeq(s, 1, i) \o <<s[i]>> \o SubSeq(s, i + 1, Len(s))
Swap(s, i)   == [s EXCEPT ![i] = s[i + 1], ![i + 1] = s[i]]

------------------------------------------------------------------------------------------
\* Type and bound invariants

TypeOK ==
    /\ envQ \in Seq(Values)
    /\ count \in 0..MaxProposals
    /\ proposed \subseteq Values
    /\ sVal \in Values
    /\ sBit \in Bits
    /\ sAcked \in BOOLEAN
    /\ rVal \in Values
    /\ rBit \in Bits
    /\ msgQ \in Seq(Msgs)
    /\ ackQ \in Seq(Bits)

QueueBound ==
    /\ Len(envQ) <= QLen
    /\ Len(msgQ) <= MaxChan
    /\ Len(ackQ) <= MaxChan

------------------------------------------------------------------------------------------
\* Initial state: sender and receiver agree on an initial proposed value

Init ==
    /\ envQ = <<>>
    /\ count = 0
    /\ sVal \in Values
    /\ proposed = {sVal}
    /\ sBit = 0
    /\ sAcked = TRUE
    /\ rVal = sVal
    /\ rBit = 0
    /\ msgQ = <<>>
    /\ ackQ = <<>>

------------------------------------------------------------------------------------------
\* Environment

Propose(v) ==
    /\ Len(envQ) < QLen
    /\ count < MaxProposals
    /\ envQ' = Append(envQ, v)
    /\ count' = count + 1
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED <<sVal, sBit, sAcked, rVal, rBit, msgQ, ackQ>>

\* Sender

Accept ==
    /\ sAcked
    /\ envQ # <<>>
    /\ sVal' = Head(envQ)
    /\ sBit' = Flip(sBit)
    /\ sAcked' = FALSE
    /\ envQ' = Tail(envQ)
    /\ UNCHANGED <<count, proposed, rVal, rBit, msgQ, ackQ>>

SendMsg ==
    /\ Len(msgQ) < MaxChan
    /\ msgQ' = Append(msgQ, <<sVal, sBit>>)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, ackQ>>

RcvAck ==
    /\ ackQ # <<>>
    /\ sAcked' = (sAcked \/ Head(ackQ) = sBit)
    /\ ackQ' = Tail(ackQ)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, rVal, rBit, msgQ>>

\* Receiver

RcvMsg ==
    /\ msgQ # <<>>
    /\ LET m == Head(msgQ) IN
         IF m[2] # rBit
           THEN /\ rVal' = m[1]
                /\ rBit' = m[2]
           ELSE UNCHANGED <<rVal, rBit>>
    /\ msgQ' = Tail(msgQ)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, ackQ>>

SendAck ==
    /\ Len(ackQ) < MaxChan
    /\ ackQ' = Append(ackQ, rBit)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, msgQ>>

\* Unreliable channels: loss, duplication, reordering (among same-tag messages)

LoseMsg ==
    /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(msgQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, ackQ>>

DupMsg ==
    /\ Len(msgQ) < MaxChan
    /\ \E i \in 1..Len(msgQ) : msgQ' = Dup(msgQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, ackQ>>

ReorderMsg ==
    /\ \E i \in 1..(Len(msgQ) - 1) :
         /\ msgQ[i][2] = msgQ[i + 1][2]
         /\ msgQ' = Swap(msgQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, ackQ>>

LoseAck ==
    /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(ackQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, msgQ>>

DupAck ==
    /\ Len(ackQ) < MaxChan
    /\ \E i \in 1..Len(ackQ) : ackQ' = Dup(ackQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, msgQ>>

ReorderAck ==
    /\ \E i \in 1..(Len(ackQ) - 1) :
         /\ ackQ[i] = ackQ[i + 1]
         /\ ackQ' = Swap(ackQ, i)
    /\ UNCHANGED <<envQ, count, proposed, sVal, sBit, sAcked, rVal, rBit, msgQ>>

------------------------------------------------------------------------------------------

Next ==
    \/ \E v \in Values : Propose(v)
    \/ Accept
    \/ SendMsg
    \/ RcvAck
    \/ RcvMsg
    \/ SendAck
    \/ LoseMsg
    \/ DupMsg
    \/ ReorderMsg
    \/ LoseAck
    \/ DupAck
    \/ ReorderAck

Fairness ==
    /\ WF_vars(Accept)
    /\ WF_vars(SendMsg)
    /\ WF_vars(SendAck)
    /\ SF_vars(RcvMsg)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------------
\* Safety

\* When tags agree, values agree: the receiver never adopts a stale/duplicate value
TagsAgreeValuesAgree == (rBit = sBit) => (rVal = sVal)

\* Delivered and accepted values always come from the proposed values
DeliveredFromProposed ==
    /\ rVal \in proposed
    /\ sVal \in proposed
    /\ \A m \in {msgQ[i] : i \in 1..Len(msgQ)} : m[1] \in proposed

\* The sender believes in an acknowledgment only if it is true
AckSound == sAcked => (rBit = sBit /\ rVal = sVal)

Safety ==
    /\ TypeOK
    /\ QueueBound
    /\ TagsAgreeValuesAgree
    /\ DeliveredFromProposed
    /\ AckSound

------------------------------------------------------------------------------------------
\* Liveness

\* Every accepted proposal is eventually adopted, or superseded by a later accepted one
AcceptedEventuallyAdoptedOrSuperseded ==
    \A v \in Values, b \in Bits :
        (sVal = v /\ sBit = b) ~> ((rVal = v /\ rBit = b) \/ sBit # b)

\* Every accepted proposal is eventually adopted by the receiver
AcceptedEventuallyAdopted ==
    \A v \in Values, b \in Bits :
        (sVal = v /\ sBit = b) ~> (rVal = v /\ rBit = b)

\* Every proposal waiting in the environment queue is eventually accepted or the
\* receiver eventually catches up with the sender
ProgressOfProposals ==
    (envQ # <<>>) ~> (sAcked /\ envQ = <<>>) \/ (envQ # <<>> /\ ~sAcked)

Agree == rVal = sVal /\ rBit = sBit

Quiescent == count = MaxProposals /\ envQ = <<>>

\* When new proposals stop arriving, the receiver infinitely often equals the sender
EventualAgreement == <>[]Quiescent => []<>Agree

Liveness ==
    /\ AcceptedEventuallyAdoptedOrSuperseded
    /\ AcceptedEventuallyAdopted
    /\ EventualAgreement

THEOREM Spec => []Safety
THEOREM Spec => Liveness

==========================================================================================