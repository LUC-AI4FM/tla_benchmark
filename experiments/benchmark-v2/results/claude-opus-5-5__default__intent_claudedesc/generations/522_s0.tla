------------------------------- MODULE AlternatingBit -------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

ASSUME Data # {}

VARIABLES AVar,   \* Sender state: <<data, bit>>
          BVar,   \* Receiver state: <<data, bit>> (last accepted message)
          AtoB,   \* Channel sender -> receiver: sequence of <<data, bit>>
          BtoA    \* Channel receiver -> sender: sequence of bits

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}

Messages == Data \X Bits

Flip(b) == 1 - b

-----------------------------------------------------------------------------
TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ AtoB \in Seq(Messages)
    /\ BtoA \in Seq(Bits)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

-----------------------------------------------------------------------------
\* Sender repeatedly (re)transmits its current message.
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

\* Sender receives an acknowledgment. If it matches its bit, it picks new
\* data and flips its bit; otherwise it ignores the ack.
ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
         THEN \E d \in Data : AVar' = <<d, Flip(AVar[2])>>
         ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

\* Receiver continuously sends an acknowledgment with its current bit.
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

\* Receiver accepts a message only if its bit differs from the current bit.
BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
         THEN BVar' = Head(AtoB)
         ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

\* Remove the element at an arbitrary position i of sequence s.
RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Lose an arbitrary message from a channel.
LoseMsg(c) ==
    /\ \E i \in 1..Len(c) : c' = RemoveAt(c, i)
    /\ UNCHANGED <<AVar, BVar>>

LoseAtoB ==
    /\ LoseMsg(AtoB)
    /\ UNCHANGED BtoA

LoseBtoA ==
    /\ LoseMsg(BtoA)
    /\ UNCHANGED AtoB

Lose == LoseAtoB \/ LoseBtoA

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ Lose

-----------------------------------------------------------------------------
Fairness ==
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: when the bits agree, the receiver holds exactly the sender's data.
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

SafetyInv == TypeOK /\ Inv

\* Liveness: every message held by the sender is eventually accepted by the receiver.
Delivery == \A v \in Messages : (AVar = v) ~> (BVar = v)

\* Liveness: the sender's bit keeps changing, i.e. new data is acknowledged
\* and new data is selected infinitely often.
Progress == \A b \in Bits : (AVar[2] = b) ~> (AVar[2] # b)

Liveness == Delivery /\ Progress

THEOREM Spec => []SafetyInv
THEOREM Spec => Liveness
=============================================================================