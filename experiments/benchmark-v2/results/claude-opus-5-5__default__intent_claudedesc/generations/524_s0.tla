------------------------------ MODULE AlternatingBit ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data            \* The set of data values that can be sent (model parameter)

ASSUME Data # {}

VARIABLES AVar,          \* Sender's current message <<data, bit>>
          BVar,          \* Receiver's last accepted message <<data, bit>>
          AtoB,          \* Lossy channel from sender to receiver (seq of <<data, bit>>)
          BtoA           \* Lossy channel from receiver to sender (seq of bits)

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}
Msgs == Data \X Bits

-----------------------------------------------------------------------------------
\* Helper: remove the i-th element of a sequence
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq(Bits)

-----------------------------------------------------------------------------------
\* Initially sender and receiver are synchronized on the same message, channels empty.
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

\* Sender (re)transmits its current message.
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

\* Sender receives an acknowledgment. If the ack bit matches its current bit,
\* the current message was delivered: a new externally provided data value is
\* queued for transmission with the flipped bit. Otherwise the ack is discarded.
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

\* Receiver (re)sends an acknowledgment with the bit of the last accepted message.
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

\* Receiver receives a message. If its bit differs from the last accepted bit,
\* the new data is accepted; otherwise it is a duplicate and is discarded.
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

\* Channels may lose any message at any time.
LoseMsg == /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
           /\ UNCHANGED <<AVar, BVar, BtoA>>

LoseAck == /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
           /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ LoseAck

Fairness == /\ WF_vars(ASnd)
            /\ WF_vars(BSnd)
            /\ SF_vars(ARcv)
            /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------
\* Correctness properties

\* Agreement: when sender and receiver have matching bits, they agree on the data.
Agreement == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Every message in flight from A to B is either the old (already accepted) message
\* or the sender's current message.
ChannelInv == \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}

Inv == TypeOK /\ Agreement /\ ChannelInv

\* Safety: the receiver's data only changes to a value actually sent by the sender.
DeliverySafety == [][BVar' # BVar => BVar' = AVar]_BVar

\* Liveness: any message queued by the sender is eventually delivered to the receiver.
Liveness == \A v \in Msgs : (AVar = v) ~> (BVar = v)

\* Bounding constraint for finite model checking with TLC (not part of the spec).
CONSTANT MaxQLen
ChannelBound == Len(AtoB) <= MaxQLen /\ Len(BtoA) <= MaxQLen

THEOREM Spec => []Inv
THEOREM Spec => DeliverySafety
THEOREM Spec => Liveness
===================================================================================