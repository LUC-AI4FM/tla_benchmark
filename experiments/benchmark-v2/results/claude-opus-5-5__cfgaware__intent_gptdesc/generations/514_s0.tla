------------------------------- MODULE AlternatingBit -------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar,   \* sender state: <<current data item, current bit>>
          BVar,   \* receiver state: <<last delivered data item, last delivered bit>>
          AtoB,   \* channel from sender to receiver (sequence of messages)
          BtoA    \* channel from receiver to sender (sequence of ack bits)

vars == <<AVar, BVar, AtoB, BtoA>>

\* A message carries a single data payload and a one-bit sequence value.
Msgs == Data \X {0, 1}

\* Bound on the number of in-flight messages per channel (keeps the model finite).
MaxLen == 2

\* Remove the i-th element of sequence s (models message loss).
Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq({0, 1})

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

-----------------------------------------------------------------------------
\* Sender (re)transmits its current message, possibly repeatedly (duplication).
ASnd ==
    /\ Len(AtoB) < MaxLen
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

\* Sender receives an acknowledgement. Only when the ack carries the current
\* bit does the sender know the receiver accepted the item, so it advances.
ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
          THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
          ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

\* Receiver (re)transmits an acknowledgement of the last delivered bit.
BSnd ==
    /\ Len(BtoA) < MaxLen
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

\* Receiver accepts a message only if its bit differs from the last delivered
\* bit; otherwise it discards it as a duplicate.
BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
          THEN BVar' = Head(AtoB)
          ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

\* Reception actions that make progress (new item / fresh ack).
BRcvNew == /\ AtoB # << >>
           /\ Head(AtoB)[2] # BVar[2]
           /\ BRcv

ARcvNew == /\ BtoA # << >>
           /\ Head(BtoA) = AVar[2]
           /\ ARcv

\* The channel may lose any message in transit.
LoseMsg ==
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
          /\ BtoA' = BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
          /\ AtoB' = AtoB
    /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

\* Fairness: the sender and receiver keep retransmitting, and the channel
\* eventually delivers some retransmission.
Fairness ==
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)
    /\ SF_vars(ARcvNew)
    /\ SF_vars(BRcvNew)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Correctness properties

\* Core protocol invariant: if the bits agree, the receiver has delivered
\* exactly the sender's current item; any in-flight message with a bit that
\* differs from the receiver's bit is the sender's current message.
Inv ==
    /\ TypeOK
    /\ (AVar[2] = BVar[2]) => (AVar = BVar)
    /\ \A i \in 1..Len(AtoB) : AtoB[i][2] # BVar[2] => AtoB[i] = AVar
    /\ \A i \in 1..Len(BtoA) : BtoA[i] = AVar[2] => BVar = AVar

\* Safety / no spurious deliveries / ordering: the receiver only ever delivers
\* the sender's current item (which was sent), and the sender only advances to
\* the next item after the current one has been delivered. Hence the delivered
\* sequence equals the produced sequence, each item delivered exactly once.
DeliverySafety ==
    [][ /\ (BVar' # BVar) => (BVar' = AVar)
        /\ (AVar' # AVar) => (AVar = BVar) ]_<<AVar, BVar>>

\* Bit alternation: successive accepted messages carry alternating bits, and
\* the sender alternates its bit on every new item.
BitAlternation ==
    [][ /\ (BVar' # BVar) => (BVar'[2] = 1 - BVar[2])
        /\ (AVar' # AVar) => (AVar'[2] = 1 - AVar[2]) ]_<<AVar, BVar>>

\* Liveness: every item the sender produces is eventually delivered.
EventualDelivery ==
    \A v \in Msgs : (AVar = v) ~> (BVar = v)

\* Progress of the sender: it eventually moves on to a new item.
SenderProgress ==
    \A b \in {0, 1} : (AVar[2] = b) ~> (AVar[2] # b)

THEOREM Spec => []Inv
THEOREM Spec => DeliverySafety
THEOREM Spec => BitAlternation
THEOREM Spec => EventualDelivery
=============================================================================