------------------------- MODULE AlternatingBitProtocol -------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data          \* set of data values that may be transmitted

ASSUME Data # {}

Bits == {0, 1}
Msg  == Data \X Bits    \* a message is a data value tagged with a bit

MaxChanLen == 3         \* bound on channel length for model checking

VARIABLES
    sender,     \* message the sender is currently trying to transmit
    receiver,   \* last message accepted by the receiver
    msgC,       \* channel from sender to receiver (sequence of messages)
    ackC        \* channel from receiver to sender (sequence of bits)

vars == <<sender, receiver, msgC, ackC>>

-----------------------------------------------------------------------------
(* Helper operators on channels                                              *)
-----------------------------------------------------------------------------

\* Remove the element at position i
Remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* Duplicate the element at position i (the copy is placed adjacent to it)
Duplicate(s, i) == SubSeq(s, 1, i) \o SubSeq(s, i, Len(s))

\* A sequence contains at most two distinct values, appearing in contiguous
\* groups: a prefix equal to the first element followed by a suffix equal to
\* the last element.
TwoValues(s) ==
    \E i \in 0..Len(s) :
        \A j \in 1..Len(s) :
            /\ (j <= i) => (s[j] = s[1])
            /\ (j > i)  => (s[j] = s[Len(s)])

-----------------------------------------------------------------------------
(* Initial state                                                              *)
-----------------------------------------------------------------------------

Init ==
    /\ \E d \in Data :
         /\ sender   = <<d, 1>>
         /\ receiver = <<d, 1>>
    /\ msgC = << >>
    /\ ackC = << >>

-----------------------------------------------------------------------------
(* Sender actions                                                             *)
-----------------------------------------------------------------------------

\* Sender (re)transmits its current message
SndSend ==
    /\ Len(msgC) < MaxChanLen
    /\ msgC' = Append(msgC, sender)
    /\ UNCHANGED <<sender, receiver, ackC>>

\* Sender receives an acknowledgment; if it matches the current bit,
\* it picks a new data value and flips its bit.
SndRcvAck ==
    /\ ackC # << >>
    /\ ackC' = Tail(ackC)
    /\ IF Head(ackC) = sender[2]
         THEN \E d \in Data : sender' = <<d, 1 - sender[2]>>
         ELSE UNCHANGED sender
    /\ UNCHANGED <<receiver, msgC>>

-----------------------------------------------------------------------------
(* Receiver actions                                                           *)
-----------------------------------------------------------------------------

\* Receiver accepts a message; a new bit means a new message.
RcvRcvMsg ==
    /\ msgC # << >>
    /\ msgC' = Tail(msgC)
    /\ IF Head(msgC)[2] # receiver[2]
         THEN receiver' = Head(msgC)
         ELSE UNCHANGED receiver
    /\ UNCHANGED <<sender, ackC>>

\* Receiver (re)sends an acknowledgment for its last accepted message
RcvSendAck ==
    /\ Len(ackC) < MaxChanLen
    /\ ackC' = Append(ackC, receiver[2])
    /\ UNCHANGED <<sender, receiver, msgC>>

-----------------------------------------------------------------------------
(* Unreliable channel actions                                                 *)
-----------------------------------------------------------------------------

LoseMsg ==
    /\ \E i \in 1..Len(msgC) : msgC' = Remove(msgC, i)
    /\ UNCHANGED <<sender, receiver, ackC>>

LoseAck ==
    /\ \E i \in 1..Len(ackC) : ackC' = Remove(ackC, i)
    /\ UNCHANGED <<sender, receiver, msgC>>

DupMsg ==
    /\ Len(msgC) < MaxChanLen
    /\ \E i \in 1..Len(msgC) : msgC' = Duplicate(msgC, i)
    /\ UNCHANGED <<sender, receiver, ackC>>

DupAck ==
    /\ Len(ackC) < MaxChanLen
    /\ \E i \in 1..Len(ackC) : ackC' = Duplicate(ackC, i)
    /\ UNCHANGED <<sender, receiver, msgC>>

-----------------------------------------------------------------------------
(* Specification                                                              *)
-----------------------------------------------------------------------------

Next ==
    \/ SndSend
    \/ SndRcvAck
    \/ RcvRcvMsg
    \/ RcvSendAck
    \/ LoseMsg
    \/ LoseAck
    \/ DupMsg
    \/ DupAck

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Correctness properties                                                     *)
-----------------------------------------------------------------------------

\* 1. Type safety
TypeOK ==
    /\ sender   \in Msg
    /\ receiver \in Msg
    /\ msgC     \in Seq(Msg)
    /\ ackC     \in Seq(Bits)

\* 2. Agreement: a pending ack matching the sender's bit implies the
\*    receiver holds exactly the sender's current message.
Agreement ==
    (\E i \in 1..Len(ackC) : ackC[i] = sender[2]) => (sender = receiver)

\* 3. Channel structure: each channel holds at most two distinct values
\*    in contiguous groups.
ChannelsTwoValues ==
    /\ TwoValues(msgC)
    /\ TwoValues(ackC)

\* Combined invariant
Inv ==
    /\ TypeOK
    /\ Agreement
    /\ ChannelsTwoValues

\* Model checking state constraint (also enforced by action guards)
StateConstraint ==
    /\ Len(msgC) <= MaxChanLen
    /\ Len(ackC) <= MaxChanLen

THEOREM Spec => [](TypeOK /\ Agreement /\ ChannelsTwoValues)
=============================================================================