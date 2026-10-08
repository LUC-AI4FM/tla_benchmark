--------------------------- MODULE FastPaxos ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT ReplicaSet, FastQuorumSets, ClassicQuorumSets
VARIABLE proposedValues, decidedValue, roundNumber, fastRoundValues, classicRoundValues

TypeOK == /\ proposedValues \in [ReplicaSet -> Nat]
          /\ decidedValue \in Nat \cup {<<None>>}
          /\ roundNumber \in Nat
          /\ fastRoundValues \in [FastQuorumSets -> Nat]
          /\ classicRoundValues \in [ClassicQuorumSets -> Nat]

FastTypeOK == TypeOK

Nontriviality == decidedValue \in proposedValues[ReplicaSet]

PaxosConsistency == 
  /\ ~<<decidedValue>> \in proposedValues[ReplicaSet] 
  /\ (decidedValue # <<None>>) => (decidedValue \in fastRoundValues[FastQuorumSets] \/ decidedValue \in classicRoundValues[ClassicQuorumSets])

FastSpec == 
  /\ TypeOK
  /\ [][TypeOK' => TypeOK]
  /\ WF_Vars(proposedValues, decidedValue, roundNumber, fastRoundValues, classicRoundValues)
  /\ SF_Vars(proposedValues, decidedValue, roundNumber, fastRoundValues, classicRoundValues)

THEOREM FastSpec => []PaxosConsistency
=============================================================================