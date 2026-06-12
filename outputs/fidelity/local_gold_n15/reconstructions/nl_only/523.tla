---- MODULE AugmentedSession ----
EXTENDS Session11projimpl, Sequences, FiniteSets

CONSTANTS MaxQueueLen

VARIABLES AtoB, BtoA, NewValQueue, AVar, BVar

Init == 
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ NewValQueue = << >>
  /\ AVar.bit = FALSE
  /\ BVar.bit = FALSE

Next ==
  \/ [][Propose \o NextA]_<<NewProposal>>
  \/ [][Acknowledge \o NextB]_<<NewAcknowledgment>>

StateConstraint ==
  /\ Len(AtoB) <= MaxQueueLen
  /\ Len(BtoA) <= MaxQueueLen
  /\ Len(NewValQueue) <= MaxQueueLen

TypeOK ==
  /\ AtoB \in Seq(Message)
  /\ BtoA \in Seq(Message)
  /\ NewValQueue \in Seq(Values)
  /\ AVar \in [bit: BOOLEAN]
  /\ BVar \in [bit: BOOLEAN]

Invariant ==
  \/ ~(\E msg \in BtoA : msg.bit = AVar.bit)
  \/ (\E msg \in BtoA : msg.bit = AVar.bit) => (\A val \in NewValQueue : val <> AVar.value)

TwoValsSeq(seq) ==
  /\ seq \in Seq(Values)
  /\ Len(seq) >= 2

Spec ==
  INSTANCE Session11projspec WITH Spec <- (Init /\ [][Next]_<<NewProposal, NewAcknowledgment>> /\ StateConstraint /\ TypeOK),
                                 Invariant <- Invariant,
                                 TwoValsSeq <- TwoValsSeq
========================================