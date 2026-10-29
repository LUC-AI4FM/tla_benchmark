---- MODULE AlternatingBit ----
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME Data # {}

VARIABLES AVar,  \* sender's current message <<data, bit>>
          BVar,  \* receiver's last accepted message <<data, bit>>
          AtoB,  \* FIFO channel sender -> receiver (lossy)
          BtoA   \* FIFO channel receiver -> sender (lossy)

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}
Msgs == Data \X Bits

-----------------------------------------------------------------------------
\* Helper: remove the i-th element of a sequence
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

-----------------------------------------------------------------------------
TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq(Bits)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

\* Sender (re)transmits its current message
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

\* Sender receives an ack; if it matches the current bit, move to new data with flipped bit
ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
          THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
          ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

\* Receiver (re)sends acknowledgment of the bit of its last accepted message
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

\* Receiver receives a data message; accepts it if the bit differs from its last one
BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
          THEN BVar' = Head(AtoB)
          ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

\* Lossy environment: arbitrary message loss on either channel
LoseMsgAtoB ==
    /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

LoseMsgBtoA ==
    /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
    /\ UNCHANGED <<AVar, BVar, AtoB>>

LoseMsg == LoseMsgAtoB \/ LoseMsgBtoA

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == Spec
            /\ SF_vars(ARcv) /\ SF_vars(BRcv)
            /\ WF_vars(ASnd) /\ WF_vars(BSnd)

-----------------------------------------------------------------------------
\* Safety / agreement invariant
Inv ==
    /\ TypeOK
    \* sender and receiver either agree, or the sender is exactly one step ahead with a flipped bit
    /\ (AVar = BVar) \/ (AVar[2] # BVar[2])
    \* receiver only holds data the sender has sent: data channel contains only current/previous messages
    /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
    \* FIFO ordering: old messages precede new ones (no reordering => no stale acceptance)
    /\ \A i, j \in 1..Len(AtoB) :
          (i < j /\ AtoB[i] = AVar) => AtoB[j] = AVar
    \* ack channel consistency
    /\ (AVar # BVar) => \A i \in 1..Len(BtoA) : BtoA[i] = BVar[2]
    /\ (AVar = BVar) => \A i, j \in 1..Len(BtoA) :
          (i < j /\ BtoA[i] = AVar[2]) => BtoA[j] = AVar[2]

Agreement == (AVar = BVar) \/ (AVar[2] # BVar[2])

-----------------------------------------------------------------------------
\* Higher-level specification of reliable data transfer (over the same variables AVar, BVar)
HighInit ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar

\* Sender produces a new data item once the previous one has been delivered
HighA ==
    /\ AVar = BVar
    /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
    /\ BVar' = BVar

\* Receiver delivers the pending data item exactly once
HighB ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ AVar' = AVar

HighNext == HighA \/ HighB

HighSpec == HighInit /\ [][HighNext]_<<AVar, BVar>>

HighFairSpec == HighSpec /\ WF_<<AVar, BVar>>(HighB)

\* Safety refinement: in-order, no-duplication, only-sent-data delivery
Refinement == HighSpec

\* Liveness: every sent data item is eventually delivered
Delivery == (AVar # BVar) ~> (AVar = BVar)

THEOREM Spec => []Inv
THEOREM Spec => HighSpec
THEOREM FairSpec => Delivery
=============================================================================