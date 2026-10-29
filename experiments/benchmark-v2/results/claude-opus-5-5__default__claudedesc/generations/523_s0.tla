---------------------------- MODULE MCAlternatingBitEnv ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Fred, Mary, Ted

Data == {Fred, Mary, Ted}

VARIABLES AVar, BVar, NewValQueue, AtoB, BtoA

vars == <<AVar, BVar, NewValQueue, AtoB, BtoA>>

Bits == {0, 1}
Msgs == Data \X Bits

-----------------------------------------------------------------------------
(* Implementation: alternating bit protocol with environment               *)
-----------------------------------------------------------------------------

Init ==
    /\ \E d \in Data : AVar = <<d, 1>>
    /\ BVar = AVar
    /\ NewValQueue = <<>>
    /\ AtoB = <<>>
    /\ BtoA = <<>>

\* Environment proposes a new data value
EnvPropose ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

\* A (re)sends its current message
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, NewValQueue, BtoA>>

\* A receives an acknowledgment; if it acknowledges the current bit and a
\* new value is available, A moves on to the next value with flipped bit.
ARcv ==
    /\ BtoA # <<>>
    /\ BtoA' = Tail(BtoA)
    /\ IF Head(BtoA) = AVar[2] /\ NewValQueue # <<>>
          THEN /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
               /\ NewValQueue' = Tail(NewValQueue)
          ELSE UNCHANGED <<AVar, NewValQueue>>
    /\ UNCHANGED <<BVar, AtoB>>

\* B (re)sends acknowledgment of its current bit
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, NewValQueue, AtoB>>

\* B receives a message; accepts it if the bit differs from its current bit
BRcv ==
    /\ AtoB # <<>>
    /\ AtoB' = Tail(AtoB)
    /\ IF Head(AtoB)[2] # BVar[2]
          THEN BVar' = Head(AtoB)
          ELSE UNCHANGED BVar
    /\ UNCHANGED <<AVar, NewValQueue, BtoA>>

RemoveElt(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Message loss on either channel
LoseMsg ==
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
          /\ UNCHANGED BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
          /\ UNCHANGED AtoB
    /\ UNCHANGED <<AVar, BVar, NewValQueue>>

Next == EnvPropose \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint for model checking                                     *)
-----------------------------------------------------------------------------

SeqConstraint ==
    /\ Len(NewValQueue) <= 3
    /\ Len(AtoB) <= 3
    /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

ABE_TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ NewValQueue \in Seq(Data)
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq(Bits)

\* Any acknowledgment in transit carrying A's current bit implies that
\* A and B agree.  (May be violated if the environment proposes values
\* faster than the protocol synchronizes.)
ABE_Inv ==
    /\ \A i \in 1..Len(BtoA) : BtoA[i] = AVar[2] => AVar = BVar
    /\ (AVar[2] = BVar[2]) => (AVar = BVar)

\* A sequence consists of at most two groups of consecutive equal values
TwoGroups(s) ==
    Cardinality({i \in 1..(Len(s) - 1) : s[i] # s[i + 1]}) <= 1

ABE_TwoValsSeq ==
    /\ TwoGroups(AtoB)
    /\ TwoGroups(BtoA)

-----------------------------------------------------------------------------
(* Abstract (high-level) specification and refinement property             *)
-----------------------------------------------------------------------------

ABESInit ==
    /\ \E d \in Data : AVar = <<d, 1>>
    /\ BVar = AVar
    /\ NewValQueue = <<>>

ABESEnv ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED <<AVar, BVar>>

ABESA ==
    /\ AVar = BVar
    /\ NewValQueue # <<>>
    /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
    /\ NewValQueue' = Tail(NewValQueue)
    /\ UNCHANGED BVar

ABESB ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ UNCHANGED <<AVar, NewValQueue>>

ABESNext == ABESEnv \/ ABESA \/ ABESB

ABESpec == ABESInit /\ [][ABESNext]_<<AVar, BVar, NewValQueue>>

ABESpecProperty == ABESpec

=============================================================================