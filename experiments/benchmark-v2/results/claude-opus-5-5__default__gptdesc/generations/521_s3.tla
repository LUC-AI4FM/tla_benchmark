------------------------------- MODULE MCSession11afair -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

\* Concrete constant data for model checking (substitute for Data in the config)
MCData == {"d1", "d2"}

\* Bound on channel lengths used by the state constraint
MaxQLen == 3

----------------------------------------------------------------------------------------
\* Two-party message exchange (alternating bit protocol)

Messages == Data \X {0, 1}

RemoveIth(seq, i) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

ASnd ==
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
  \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
     /\ UNCHANGED <<AVar, BVar, BtoA>>
  \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
     /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

----------------------------------------------------------------------------------------
\* State constraint: bound message queue lengths

SeqConstraint == /\ Len(AtoB) <= MaxQLen
                 /\ Len(BtoA) <= MaxQLen

----------------------------------------------------------------------------------------
\* Derived predicates about communication variables and channels

TypeOK ==
  /\ AVar \in Messages
  /\ BVar \in Messages
  /\ AtoB \in Seq(Messages)
  /\ BtoA \in Seq({0, 1})

\* Every message in AtoB is either the current AVar or a single older message
\* (with the opposite bit) that precedes all copies of AVar.
AtoBStructure ==
  \A i \in 1..Len(AtoB) :
     \/ AtoB[i] = AVar
     \/ /\ AtoB[i][2] # AVar[2]
        /\ \A j \in 1..i : AtoB[j] = AtoB[i]

\* BtoA contains at most one change of bit value.
BtoAStructure ==
  \A i \in 1..(Len(BtoA) - 1) :
     BtoA[i] # BtoA[i + 1] =>
        \A j \in (i + 1)..Len(BtoA) : BtoA[j] = BtoA[i + 1]

Inv == TypeOK /\ AtoBStructure /\ BtoAStructure

----------------------------------------------------------------------------------------
\* The fair high-level specification (as in Session11afair), over AVar and BVar

ABSvars == <<AVar, BVar>>

ABSInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar

ABSA ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
  /\ BVar' = BVar

ABSB ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ AVar' = AVar

ABSNext == ABSA \/ ABSB

ABSSpec == ABSInit /\ [][ABSNext]_ABSvars /\ WF_ABSvars(ABSNext)

ABSpecProperty == ABSSpec

----------------------------------------------------------------------------------------
\* Liveness: every value A holds is eventually delivered to B

Liveness == \A v \in Messages : (AVar = v) ~> (BVar = v)

=========================================================================================