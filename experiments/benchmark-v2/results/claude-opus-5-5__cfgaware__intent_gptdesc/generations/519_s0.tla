---- MODULE AB2 ----
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

ConstData == {"d1", "d2"}

MaxLen == 3

Bits == {0, 1}

Msgs == Data \X Bits

Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

AB2_TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq(Bits)
  /\ Len(AtoB) <= MaxLen
  /\ Len(BtoA) <= MaxLen

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

ASnd ==
  /\ Len(AtoB) < MaxLen
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVar, AtoB>>

BSnd ==
  /\ Len(BtoA) < MaxLen
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA>>

LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

StateConstraint ==
  /\ Len(AtoB) <= MaxLen
  /\ Len(BtoA) <= MaxLen

ChannelBounds == StateConstraint

BitsAgree == (AVar[2] = BVar[2]) <=> (AVar = BVar)

NoSpuriousDuplicates ==
  [][(BVar' # BVar) => (BVar' = AVar /\ BVar'[2] # BVar[2])]_vars

Liveness ==
  /\ \A v \in Msgs : (AVar = v) ~> (BVar = v \/ AVar # v)
  /\ \A v \in Msgs : (AVar = v /\ BVar = v) ~> (AVar # v)

Rec(t) == [data |-> t[1], bit |-> t[2]]

AVarBar == Rec(AVar)
BVarBar == Rec(BVar)
AtoBBar == [i \in 1..Len(AtoB) |-> Rec(AtoB[i])]

absVars == <<AVarBar, BVarBar, AtoBBar, BtoA>>

AbsInit ==
  /\ AVarBar \in [data : Data, bit : {1}]
  /\ BVarBar = AVarBar
  /\ AtoBBar = << >>
  /\ BtoA = << >>

AbsASnd ==
  /\ AtoBBar' = Append(AtoBBar, AVarBar)
  /\ UNCHANGED <<AVarBar, BVarBar, BtoA>>

AbsARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVarBar.bit
       THEN \E d \in Data : AVarBar' = [data |-> d, bit |-> 1 - AVarBar.bit]
       ELSE AVarBar' = AVarBar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVarBar, AtoBBar>>

AbsBSnd ==
  /\ BtoA' = Append(BtoA, BVarBar.bit)
  /\ UNCHANGED <<AVarBar, BVarBar, AtoBBar>>

AbsBRcv ==
  /\ AtoBBar # << >>
  /\ IF Head(AtoBBar).bit # BVarBar.bit
       THEN BVarBar' = Head(AtoBBar)
       ELSE BVarBar' = BVarBar
  /\ AtoBBar' = Tail(AtoBBar)
  /\ UNCHANGED <<AVarBar, BtoA>>

AbsLose ==
  /\ \/ /\ \E i \in 1..Len(AtoBBar) : AtoBBar' = Remove(i, AtoBBar)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
        /\ AtoBBar' = AtoBBar
  /\ UNCHANGED <<AVarBar, BVarBar>>

AbsNext == AbsASnd \/ AbsARcv \/ AbsBSnd \/ AbsBRcv \/ AbsLose

ABSpecProperty ==
  /\ AbsInit
  /\ [][AbsNext]_absVars
  /\ WF_absVars(AbsASnd)
  /\ WF_absVars(AbsBSnd)
  /\ SF_absVars(AbsARcv)
  /\ SF_absVars(AbsBRcv)

THEOREM Spec => []AB2_TypeOK
THEOREM Spec => []ChannelBounds
THEOREM Spec => ABSpecProperty
====