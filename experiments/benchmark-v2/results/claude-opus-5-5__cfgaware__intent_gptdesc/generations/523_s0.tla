------------------------------- MODULE ABE -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Data

VARIABLES
  AVar,      \* proposer's current <<value, bit>>
  BVar,      \* acceptor's last accepted (delivered) <<value, bit>>
  AtoB,      \* forward FIFO channel: messages <<value, bit>>
  BtoA,      \* backward FIFO channel: acknowledgment bits
  buf,       \* proposer's bounded buffer of incoming proposals
  aAcked,    \* TRUE iff proposer received an ack matching its current bit
  proposed   \* set of all values ever proposed (history, for safety)

vars == <<AVar, BVar, AtoB, BtoA, buf, aAcked, proposed>>

ConstData == {"d1", "d2"}

ChanMax == 3
BufMax  == 2
Bits    == {0, 1}
Msgs    == Data \X Bits

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

-----------------------------------------------------------------------------
Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ buf = << >>
  /\ aAcked = TRUE
  /\ proposed = {AVar[1]}

\* Environment injects a new proposal, limited by the buffer bound.
Propose ==
  /\ Len(buf) < BufMax
  /\ \E d \in Data :
       /\ buf' = Append(buf, d)
       /\ proposed' = proposed \cup {d}
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA, aAcked>>

\* Proposer adopts the next buffered proposal with a flipped bit.
ANext ==
  /\ aAcked
  /\ buf # << >>
  /\ AVar' = <<Head(buf), 1 - AVar[2]>>
  /\ buf' = Tail(buf)
  /\ aAcked' = FALSE
  /\ UNCHANGED <<BVar, AtoB, BtoA, proposed>>

\* Proposer (re)transmits its latest outstanding proposal.
ASnd ==
  /\ ~aAcked
  /\ Len(AtoB) < ChanMax
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, buf, aAcked, proposed>>

\* Proposer receives an acknowledgment.
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ aAcked' = IF Head(BtoA) = AVar[2] THEN TRUE ELSE aAcked
  /\ UNCHANGED <<AVar, BVar, AtoB, buf, proposed>>

\* Acceptor sends an acknowledgment with the bit it believes current.
BSnd ==
  /\ Len(BtoA) < ChanMax
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB, buf, aAcked, proposed>>

\* Acceptor receives a message; delivers only when the bit is new.
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ BVar' = IF Head(AtoB)[2] # BVar[2] THEN Head(AtoB) ELSE BVar
  /\ UNCHANGED <<AVar, BtoA, buf, aAcked, proposed>>

\* Channels may drop messages.
LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
        /\ UNCHANGED BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar, buf, aAcked, proposed>>

Next == Propose \/ ANext \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness ==
  /\ WF_vars(ANext)
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
StateConstraint ==
  /\ Len(AtoB) <= ChanMax
  /\ Len(BtoA) <= ChanMax
  /\ Len(buf) <= BufMax

ABE_TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq(Bits)
  /\ buf \in Seq(Data)
  /\ aAcked \in BOOLEAN
  /\ proposed \in SUBSET Data

ChannelBounds ==
  /\ Len(AtoB) <= ChanMax
  /\ Len(BtoA) <= ChanMax
  /\ Len(buf) <= BufMax

\* Safety: delivered value was actually proposed; any message carrying the
\* proposer's current bit carries the proposer's current value, so the
\* acceptor can never deliver two different values for the same bit.
NonCorrupting ==
  /\ BVar[1] \in proposed
  /\ AVar[1] \in proposed
  /\ \A i \in 1..Len(AtoB) :
       /\ AtoB[i][1] \in proposed
       /\ (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)
       /\ (AtoB[i][2] # AVar[2]) => (AtoB[i][2] = BVar[2] => AtoB[i] = BVar)

\* No spurious acceptance.
NoSpuriousAcceptance ==
  (BVar[2] = AVar[2]) => (AVar[1] = BVar[1])

AckConsistent ==
  /\ aAcked => (BVar = AVar)
  /\ \A i \in 1..Len(BtoA) : (BtoA[i] = AVar[2]) => (BVar = AVar)

IsTwoValued(s) ==
  \E i \in 0..Len(s) :
    /\ \A j \in 1..i : s[j] = s[1]
    /\ \A j \in (i + 1)..Len(s) : s[j] = s[Len(s)]

TwoValues ==
  /\ IsTwoValued(AtoB)
  /\ IsTwoValued(BtoA)

Inv ==
  /\ ABE_TypeOK
  /\ ChannelBounds
  /\ NonCorrupting
  /\ NoSpuriousAcceptance
  /\ AckConsistent
  /\ TwoValues

-----------------------------------------------------------------------------
\* High-level alternating-bit specification refined by the protocol.
HInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar

HA ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
  /\ BVar' = BVar

HB ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ AVar' = AVar

HSpec == HInit /\ [][HA \/ HB]_<<AVar, BVar>> /\ WF_<<AVar, BVar>>(HB)

ABESpecProperty == HSpec

\* Liveness: every outstanding proposal is eventually accepted or superseded.
EventuallyAccepted ==
  \A d \in Data, b \in Bits :
    (AVar = <<d, b>>) ~> (BVar = <<d, b>> \/ AVar[2] # b)

\* When the proposer stops receiving new proposals, its current
\* proposal is eventually accepted and acknowledged.
StopsProposing == <>[][~Propose]_vars

EventuallyAcked ==
  StopsProposing => <>[](BVar = AVar /\ aAcked /\ buf = << >>)

=============================================================================