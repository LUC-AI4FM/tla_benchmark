---------------------------- MODULE MCABE ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue, AtoB, BtoA

vars == <<AVar, BVar, NewValQueue, AtoB, BtoA>>

ConstData == {"Fred", "Mary", "Ted"}

-----------------------------------------------------------------------------
Message == Data \X {0, 1}

ABE_TypeOK == /\ AVar \in Message
              /\ BVar \in Message
              /\ NewValQueue \in Seq(Data)
              /\ AtoB \in Seq(Message)
              /\ BtoA \in Seq({0, 1})

-----------------------------------------------------------------------------
RemoveIth(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>
        /\ AtoB = << >>
        /\ BtoA = << >>

EnvProposeVal == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
                 /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, NewValQueue, BtoA>>

ARcv == /\ BtoA # << >>
        /\ BtoA' = Tail(BtoA)
        /\ IF /\ Head(BtoA) = AVar[2]
              /\ NewValQueue # << >>
             THEN /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
                  /\ NewValQueue' = Tail(NewValQueue)
             ELSE UNCHANGED <<AVar, NewValQueue>>
        /\ UNCHANGED <<BVar, AtoB>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, NewValQueue, AtoB>>

BRcv == /\ AtoB # << >>
        /\ AtoB' = Tail(AtoB)
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ UNCHANGED <<AVar, NewValQueue, BtoA>>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar, NewValQueue>>

Next == \/ EnvProposeVal
        \/ ASnd \/ ARcv
        \/ BSnd \/ BRcv
        \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
StateConstraint == /\ Len(NewValQueue) =< 3
                   /\ Len(AtoB) =< 3
                   /\ Len(BtoA) =< 3

(* May be violated if the environment proposes values faster than the    *)
(* protocol can synchronize.                                              *)
ABE_Inv == \A i \in 1..Len(BtoA) : (BtoA[i] = AVar[2]) => (AVar = BVar)

\* Number of maximal groups of consecutive equal elements in a sequence
NumGroups(s) == Cardinality({i \in 1..Len(s) : i = 1 \/ s[i] # s[i-1]})

Cardinality(S) ==
  LET f[T \in SUBSET S] == IF T = {} THEN 0
                           ELSE 1 + f[T \ {CHOOSE x \in T : TRUE}]
  IN f[S]

TwoGroups(s) == Len(s) = 0 \/
  \E i \in 0..Len(s) :
     /\ \A j \in 1..i : s[j] = s[1]
     /\ \A j \in (i+1)..Len(s) : s[j] = s[Len(s)]

ABE_TwoValsSeq == /\ TwoGroups(AtoB)
                  /\ TwoGroups(BtoA)

-----------------------------------------------------------------------------
(* High-level alternating-bit specification *)
ABSInit == /\ AVar \in Data \X {1}
           /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABSNext == ABS_A \/ ABS_B

ABESpecProperty == ABSInit /\ [][ABSNext]_<<AVar, BVar>>

=============================================================================