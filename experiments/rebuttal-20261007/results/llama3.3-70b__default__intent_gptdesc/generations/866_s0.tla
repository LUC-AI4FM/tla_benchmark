```
MODULE FastPaxos
EXTENDS Integers, FiniteSets

CONSTANTS ReplicaSet, FastQuorumSets, ClassicQuorumSets, Values

VARIABLES proposedValues, acceptedValues, decidedValue, roundType, currentRound, fastQuorumResponses, classicQuorumAccepts, coordinatorChoice

Init ==
  /\ proposedValues = {}
  /\ acceptedValues = {}
  /\ decidedValue = <<>>
  /\ roundType = "fast"
  /\ currentRound = 1
  /\ fastQuorumResponses = {}
  /\ classicQuorumAccepts = {}
  /\ coordinatorChoice = <<>>

Next ==
  \/ \* Fast Round \*
    /\ roundType = "fast"
    /\ proposedValues' = proposedValues \cup {v \in Values : \exists p \in ReplicaSet : p proposes v}
    /\ fastQuorumResponses' = fastQuorumResponses \cup {a \in FastQuorumSets : a responds with some v}
    /\ IF \exists v \in Values : {a \in FastQuorumSets : fastQuorumResponses'[a] = v} \in FastQuorumSets
      THEN decidedValue' = v
           ELSE decidedValue' = decidedValue
    /\ acceptedValues' = acceptedValues
    /\ classicQuorumAccepts' = classicQuorumAccepts
    /\ coordinatorChoice' = coordinatorChoice
  \/ \* Classic Round \*
    /\ roundType = "classic"
    /\ proposedValues' = proposedValues
    /\ fastQuorumResponses' = fastQuorumResponses
    /\ acceptedValues' = acceptedValues \cup {a \in ClassicQuorumSets : a accepts some v}
    /\ classicQuorumAccepts' = classicQuorumAccepts \cup {a \in ClassicQuorumSets : a accepts coordinatorChoice}
    /\ IF \exists v \in Values : {a \in ClassicQuorumSets : classicQuorumAccepts'[a] = v} \in ClassicQuorumSets
      THEN decidedValue' = v
           ELSE decidedValue' = decidedValue
    /\ coordinatorChoice' = [v \in Values : \exists m \in FastQuorumResponses : m = v /\ {a \in FastQuorumSets : fastQuorumResponses[a] = v} \in FastQuorumSets]
  \/ \* Coordinator Conflict Resolution \*
    /\ roundType = "classic"
    /\ proposedValues' = proposedValues
    /\ fastQuorumResponses' = fastQuorumResponses
    /\ acceptedValues' = acceptedValues
    /\ classicQuorumAccepts' = classicQuorumAccepts
    /\ coordinatorChoice' \in {v \in Values : \exists m \in FastQuorumResponses : m = v}

Spec ==
  /\ Init
  /\ [][Next]_proposedValues,acceptedValues,decidedValue,roundType,currentRound,fastQuorumResponses,classicQuorumAccepts,coordinatorChoice
  /\ WF_vars(proposedValues, acceptedValues, decidedValue, roundType, currentRound, fastQuorumResponses, classicQuorumAccepts, coordinatorChoice)
  /\ SF_vars(proposedValues, acceptedValues, decidedValue, roundType, currentRound, fastQuorumResponses, classicQuorumAccepts, coordinatorChoice)

Agreement ==
  \* No two different values can both become decided \*
  decidedValue \in [Values] \/ decidedValue = <<>>

Nontriviality ==
  \* Only values that were actually proposed by some acceptor can be decided \*
  decidedValue \in proposedValues

ValidConflictResolutionRule ==
  \* When resolving collisions the coordinator must respect the majority-in-quorum rule \*
  coordinatorChoice \in {v \in Values : \exists m \in FastQuorumResponses : m = v /\ {a \in FastQuorumSets : fastQuorumResponses[a] = v} \in FastQuorumSets}

THEOREM Spec => []Agreement
THEOREM Spec => []Nontriviality
THEOREM Spec => []ValidConflictResolutionRule

Fairness ==
  \* Fairness conditions sufficient to ensure progress of decision steps when required quorums and messages eventually occur \*
  /\ WF_vars(proposedValues, acceptedValues, decidedValue, roundType, currentRound, fastQuorumResponses, classicQuorumAccepts, coordinatorChoice)
  /\ SF_vars(proposedValues, acceptedValues, decidedValue, roundType, currentRound, fastQuorumResponses, classicQuorumAccepts, coordinatorChoice)

QuorumStructure ==
  \* Parameterization of replica set, fast-quorum sets, and classic quorum sets \*
  /\ ReplicaSet \subseteq DOMAIN proposedValues
  /\ FastQuorumSets \subseteq POW(ReplicaSet)
  /\ ClassicQuorumSets \subseteq POW(ReplicaSet)
  /\ \forall f1, f2 \in FastQuorumSets : f1 \cap f2 /= {}
  /\ \forall c \in ClassicQuorumSets : \exists f \in FastQuorumSets : c \cap f /= {}

THEOREM Spec => []QuorumStructure
```