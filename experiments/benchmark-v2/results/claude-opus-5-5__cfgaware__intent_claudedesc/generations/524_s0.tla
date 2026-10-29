------------------------- MODULE AlternatingBit -------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA, NewValQueue

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue>>

Msgs == Data \X {0, 1}

TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq({0, 1})
  /\ NewValQueue \in Seq(Data)

Init ==
  /\ \E d \in Data : /\ AVar = <<d, 1>>
                     /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ NewValQueue = << >>

\* External environment: provides a new data value when A and B are synchronized
QueueNewVal ==
  /\ AVar = BVar
  /\ NewValQueue = << >>
  /\ \E d \in Data : NewValQueue' = <<d>>
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

\* A (re)transmits its current message
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue>>

\* A receives an acknowledgment
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF /\ Head(BtoA) = AVar[2]
        /\ NewValQueue # << >>
       THEN /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
            /\ NewValQueue' = Tail(NewValQueue)
       ELSE UNCHANGED <<AVar, NewValQueue>>
  /\ UNCHANGED <<BVar, AtoB>>

\* B (re)transmits the acknowledgment of the last correctly received bit
BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

\* B receives a data message
BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA, NewValQueue>>

\* Removes the i-th element of a sequence
RemoveIth(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
        /\ UNCHANGED BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar, NewValQueue>>

Next == QueueNewVal \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Correctness properties

\* Safety: B's data only changes to values that A actually sent
SafeBChange ==
  [][BVar' # BVar => BVar' = AVar]_vars

\* Agreement: when synchronized (same bit), both agree on the data
Agreement ==
  (AVar[2] = BVar[2]) => (AVar[1] = BVar[1])

Inv == TypeOK /\ Agreement

\* Liveness: a queued new value is eventually delivered to B
E ==
  \A d \in Data :
     (NewValQueue = <<d>>) ~> (BVar[1] = d /\ BVar = AVar)

=============================================================================