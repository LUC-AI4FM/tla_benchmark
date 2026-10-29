------------------------------- MODULE AlternatingBit -------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data
ASSUME DataNonEmpty == Data # {}

Bits     == {0, 1}
Messages == Bits \X Data
Flip(b)  == 1 - b

VARIABLES
    sBit,     \* sequence bit of the current (last sent) packet at the sender
    sAck,     \* last acknowledgment bit received by the sender
    sent,     \* data item of the current packet (kept for retransmission)
    rBit,     \* bit of the last packet the receiver accepted (expected bit = Flip(rBit))
    msgC,     \* data channel: lossy FIFO sequence of <<bit, data>> pairs
    ackC,     \* acknowledgment channel: lossy FIFO sequence of bits
    input,    \* history of data items accepted by the sender from the application
    output    \* history of data items delivered by the receiver to the application

vars == <<sBit, sAck, sent, rBit, msgC, ackC, input, output>>

-----------------------------------------------------------------------------
(* Auxiliary operator: remove the i-th element of a sequence *)
Remove(i, s) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

-----------------------------------------------------------------------------
(* Type / legal-state invariant *)
TypeOK ==
    /\ sBit   \in Bits
    /\ sAck   \in Bits
    /\ sent   \in Data
    /\ rBit   \in Bits
    /\ msgC   \in Seq(Messages)
    /\ ackC   \in Seq(Bits)
    /\ input  \in Seq(Data)
    /\ output \in Seq(Data)

-----------------------------------------------------------------------------
Init ==
    /\ sBit   = 0
    /\ sAck   = 0
    /\ sent   \in Data
    /\ rBit   = 0
    /\ msgC   = << >>
    /\ ackC   = << >>
    /\ input  = << >>
    /\ output = << >>

-----------------------------------------------------------------------------
(* Sender actions *)

\* Sender accepts a new application datum when the previous packet was acknowledged
SndNewValue(d) ==
    /\ sAck = sBit
    /\ sBit'  = Flip(sBit)
    /\ sent'  = d
    /\ msgC'  = Append(msgC, <<Flip(sBit), d>>)
    /\ input' = Append(input, d)
    /\ UNCHANGED <<sAck, rBit, ackC, output>>

\* Sender retransmits the current packet when it suspects loss (not yet acknowledged)
ReSndMsg ==
    /\ sAck # sBit
    /\ msgC' = Append(msgC, <<sBit, sent>>)
    /\ UNCHANGED <<sBit, sAck, sent, rBit, ackC, input, output>>

\* Sender receives an acknowledgment bit
RcvAck ==
    /\ ackC # << >>
    /\ sAck' = Head(ackC)
    /\ ackC' = Tail(ackC)
    /\ UNCHANGED <<sBit, sent, rBit, msgC, input, output>>

-----------------------------------------------------------------------------
(* Receiver actions *)

\* Receiver accepts a packet; delivers only if its bit is the expected one
RcvMsg ==
    /\ msgC # << >>
    /\ msgC' = Tail(msgC)
    /\ LET b == Head(msgC)[1]
           d == Head(msgC)[2]
       IN  IF b # rBit
             THEN /\ rBit'   = b
                  /\ output' = Append(output, d)
             ELSE UNCHANGED <<rBit, output>>
    /\ UNCHANGED <<sBit, sAck, sent, ackC, input>>

\* Receiver sends an acknowledgment carrying the bit it last received
SndAck ==
    /\ ackC' = Append(ackC, rBit)
    /\ UNCHANGED <<sBit, sAck, sent, rBit, msgC, input, output>>

-----------------------------------------------------------------------------
(* Unreliable channels: may drop any individual message *)

LoseMsg ==
    /\ \E i \in 1..Len(msgC) : msgC' = Remove(i, msgC)
    /\ UNCHANGED <<sBit, sAck, sent, rBit, ackC, input, output>>

LoseAck ==
    /\ \E i \in 1..Len(ackC) : ackC' = Remove(i, ackC)
    /\ UNCHANGED <<sBit, sAck, sent, rBit, msgC, input, output>>

-----------------------------------------------------------------------------
Next ==
    \/ \E d \in Data : SndNewValue(d)
    \/ ReSndMsg
    \/ RcvAck
    \/ RcvMsg
    \/ SndAck
    \/ LoseMsg
    \/ LoseAck

Fairness ==
    /\ WF_vars(ReSndMsg)
    /\ WF_vars(SndAck)
    /\ SF_vars(RcvMsg)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Delivered data is never corrupted and each datum is delivered at most once,
\* in order: the delivered sequence is always a prefix of the sent sequence.
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

NoCorruptionNoDuplication == IsPrefix(output, input)

\* The receiver is never more than one item behind the sender
BoundedLag == Len(input) - Len(output) \in {0, 1}

\* Structural invariant relating sender/receiver bits to protocol progress
ProtocolInv ==
    /\ sBit = Len(input) % 2
    /\ rBit = Len(output) % 2
    /\ (sAck = sBit) => (Len(output) = Len(input))
    /\ (Len(input) > 0 /\ Len(output) = Len(input)) => (input[Len(input)] = sent)

Safety == TypeOK /\ NoCorruptionNoDuplication /\ BoundedLag

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every datum the sender has sent is eventually delivered by the receiver
EventualDelivery ==
    \A n \in Nat : (Len(input) >= n) ~> (Len(output) >= n)

\* Every outstanding packet is eventually acknowledged
EventualAck == (sAck # sBit) ~> (sAck = sBit)

Liveness == EventualDelivery /\ EventualAck

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrect   == Spec => []TypeOK
THEOREM SafetyThm     == Spec => [](NoCorruptionNoDuplication /\ BoundedLag)
THEOREM InvThm        == Spec => []ProtocolInv
THEOREM LivenessThm   == Spec => Liveness

=============================================================================