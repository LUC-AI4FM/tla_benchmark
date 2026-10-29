------------------------------ MODULE MCSession11b ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the two-party Alternating Bit message       *)
(* exchange.  Variables AVar and BVar are the values held by the sender A *)
(* and receiver B; AtoB and BtoA are lossy FIFO channels.  The wrapper    *)
(* supplies concrete constant data, a state constraint bounding queue     *)
(* lengths, typing and structural predicates on the channels, and exposes *)
(* the fair high-level specification (Session11afair) as ABSpecProperty.  *)
(* The protocol and the Session11afair spec are inlined so the module is  *)
(* self-contained.                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Data, MaxQueueLen

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

(***************************************************************************)
(* Concrete constant data for model checking (substitute in the cfg:     *)
(*   Data <- MCData, MaxQueueLen <- MCMaxQueueLen).                        *)
(***************************************************************************)
MCData == {"d1", "d2"}
MCMaxQueueLen == 3

Messages == Data \X {0, 1}

RemoveElement(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************)
(* Low-level protocol (the session module being wrapped).                 *)
(***************************************************************************)
Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv ==
  /\ BtoA /= << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVar, AtoB>>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
  /\ AtoB /= << >>
  /\ IF Head(AtoB)[2] /= BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA>>

LoseMsg ==
  \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElement(i, AtoB)
     /\ UNCHANGED <<AVar, BVar, BtoA>>
  \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElement(i, BtoA)
     /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec ==
  /\ Spec
  /\ SF_vars(ARcv) /\ SF_vars(BRcv)
  /\ WF_vars(ASnd) /\ WF_vars(BSnd)

(***************************************************************************)
(* Inlined Session11afair: the fair high-level spec over AVar and BVar.   *)
(***************************************************************************)
ABSInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar

ABSA ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
  /\ UNCHANGED BVar

ABSB ==
  /\ AVar /= BVar
  /\ BVar' = AVar
  /\ UNCHANGED AVar

ABSNext == ABSA \/ ABSB

ABSSpec ==
  /\ ABSInit
  /\ [][ABSNext]_<<AVar, BVar>>
  /\ WF_<<AVar, BVar>>(ABSNext)

(***************************************************************************)
(* Model-checking wrapper definitions.                                     *)
(***************************************************************************)
SeqConstraint ==
  /\ Len(AtoB) <= MaxQueueLen
  /\ Len(BtoA) <= MaxQueueLen

TypeOK ==
  /\ AVar \in Messages
  /\ BVar \in Messages
  /\ AtoB \in Seq(Messages)
  /\ BtoA \in Seq({0, 1})

\* Structural property: at most two distinct messages are ever in transit
\* from A to B, and at most two distinct acknowledgment bits from B to A.
AtoBStructure == Cardinality({AtoB[i] : i \in DOMAIN AtoB}) <= 2
BtoAStructure == Cardinality({BtoA[i] : i \in DOMAIN BtoA}) <= 2

\* Messages in AtoB carrying A's current bit equal A's current value.
AtoBConsistent ==
  \A i \in DOMAIN AtoB : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)

Inv ==
  /\ TypeOK
  /\ AtoBStructure
  /\ BtoAStructure
  /\ AtoBConsistent

ABSpecProperty == ABSSpec

THEOREM FairSpec => [](Inv)
THEOREM FairSpec => ABSpecProperty
=============================================================================