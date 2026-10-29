---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Data,        \* set of data values that can be transmitted
          MaxChanLen   \* bound on channel lengths (for model checking only), e.g. 3

ASSUME MaxChanLen \in Nat \ {0}
ASSUME Data # {}

VARIABLES sAck,   \* last acknowledgment bit received by the sender
          sBit,   \* sender's current alternating bit
          sent,   \* current message value the sender is transmitting
          rBit,   \* receiver's bit (bit of the last accepted message)
          rcvd,   \* last message value accepted by the receiver
          AtoB,   \* data channel: sender -> receiver, sequence of <<value, bit>>
          BtoA    \* ack channel:  receiver -> sender, sequence of bits

vars == <<sAck, sBit, sent, rBit, rcvd, AtoB, BtoA>>

Bits == {0, 1}

-----------------------------------------------------------------------------
(* Helper operators *)

Remove(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

AtoBBits == [i \in 1..Len(AtoB) |-> AtoB[i][2]]

\* A sequence in which the value changes at most once
AtMostOneChange(s) ==
    \A i \in 1..(Len(s) - 1) :
        (s[i] # s[i + 1]) => \A j \in (i + 1)..Len(s) : s[j] = s[i + 1]

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ sBit \in Bits
        /\ sAck = sBit
        /\ rBit = sBit
        /\ sent \in Data
        /\ rcvd = sent
        /\ AtoB = << >>
        /\ BtoA = << >>

-----------------------------------------------------------------------------
(* Sender actions *)

\* Sender received the correct ack: advance to next message and flip bit
A == /\ sAck = sBit
     /\ sBit' = 1 - sBit
     /\ \E d \in Data : sent' = d
     /\ UNCHANGED <<sAck, rBit, rcvd, AtoB, BtoA>>

\* Sender (re)transmits the current message tagged with its bit
SndA == /\ AtoB' = Append(AtoB, <<sent, sBit>>)
        /\ UNCHANGED <<sAck, sBit, sent, rBit, rcvd, BtoA>>

\* Sender receives an acknowledgment bit
RcvA == /\ BtoA # << >>
        /\ sAck' = Head(BtoA)
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<sBit, sent, rBit, rcvd, AtoB>>

(* Receiver actions *)

\* Receiver gets a message; accepts it only if it carries the expected bit
RcvB == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # rBit
             THEN /\ rBit' = Head(AtoB)[2]
                  /\ rcvd' = Head(AtoB)[1]
             ELSE UNCHANGED <<rBit, rcvd>>
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<sAck, sBit, sent, BtoA>>

\* Receiver (re)sends acknowledgment carrying the bit of the received message
SndB == /\ BtoA' = Append(BtoA, rBit)
        /\ UNCHANGED <<sAck, sBit, sent, rBit, rcvd, AtoB>>

(* Unreliable channel: messages may be lost (duplication arises from retransmission) *)

LoseMsgA == /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(AtoB, i)
            /\ UNCHANGED <<sAck, sBit, sent, rBit, rcvd, BtoA>>

LoseMsgB == /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(BtoA, i)
            /\ UNCHANGED <<sAck, sBit, sent, rBit, rcvd, AtoB>>

-----------------------------------------------------------------------------

Next == \/ A \/ SndA \/ RcvA
        \/ RcvB \/ SndB
        \/ LoseMsgA \/ LoseMsgB

Fairness == /\ WF_vars(SndA)
            /\ WF_vars(SndB)
            /\ SF_vars(RcvA)
            /\ SF_vars(RcvB)

Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint for model checking: bound channel lengths
SeqConstraint == /\ Len(AtoB) <= MaxChanLen
                 /\ Len(BtoA) <= MaxChanLen

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ sAck \in Bits
          /\ sBit \in Bits
          /\ rBit \in Bits
          /\ sent \in Data
          /\ rcvd \in Data
          /\ AtoB \in Seq(Data \X Bits)
          /\ BtoA \in Seq(Bits)

\* When the ack channel holds the sender's current bit (or the sender has
\* received that ack), sender and receiver agree on the current message
DataIntegrity ==
    /\ (\E i \in 1..Len(BtoA) : BtoA[i] = sBit) => (rcvd = sent)
    /\ (sAck = sBit) => (rcvd = sent)
    /\ (rBit = sBit) => (rcvd = sent)

\* Bits along the data flow path change value at most once
ChannelCoherence ==
    /\ AtMostOneChange(<<sAck>> \o BtoA \o <<rBit>> \o AtoBBits \o <<sBit>>)
    /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = sBit) => (AtoB[i][1] = sent)

Inv == TypeOK /\ DataIntegrity /\ ChannelCoherence

-----------------------------------------------------------------------------
(* High-level specification of reliable transfer, via refinement mapping *)

AVar == <<sent, sBit>>   \* value the sender wants delivered
BVar == <<rcvd, rBit>>   \* value the receiver has accepted

HInit == /\ AVar \in Data \X Bits
         /\ BVar = AVar

\* Sender hands a new value once the previous one was delivered
HA == /\ AVar = BVar
      /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
      /\ BVar' = BVar

\* Value is reliably transferred to the receiver
HB == /\ AVar # BVar
      /\ BVar' = AVar
      /\ AVar' = AVar

HNext == HA \/ HB

ABSpec == HInit /\ [][HNext]_<<AVar, BVar>> /\ WF_<<AVar, BVar>>(HB)

-----------------------------------------------------------------------------
(* Liveness *)

\* Every message the sender is transmitting is eventually received
Delivery == (AVar # BVar) ~> (AVar = BVar)

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => ABSpec
THEOREM Spec => Delivery
=============================================================================