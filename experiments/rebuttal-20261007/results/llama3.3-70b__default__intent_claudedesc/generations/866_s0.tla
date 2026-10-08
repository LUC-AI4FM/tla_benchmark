```tla
MODULE FastPaxos

EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Coordinator, Quorums
VARIABLES proposedValues, votes, decidedValue, roundType, currentRound, fastQuorumVotes

Init ==
  /\ proposedValues = {}
  /\ votes = {}
  /\ decidedValue = NULL
  /\ roundType = "fast"
  /\ currentRound = 1
  /\ fastQuorumVotes = {}

Next ==
  \/ FastRoundInitiation
  \/ FastVoting
  \/ FastDecision
  \/ CollisionRecovery
  \/ ClassicRoundExecution

FastRoundInitiation ==
  /\ roundType = "fast"
  /\ currentRound' = currentRound + 1
  /\ proposedValues' = {}
  /\ votes' = {}
  /\ fastQuorumVotes' = {}

FastVoting ==
  /\ roundType = "fast"
  /\ \E r \in Replicas : 
    /\ proposedValues' = [proposedValues EXCEPT ![r] = someValue]
    /\ someValue \in Values
    /\ votes' = [votes EXCEPT ![r] = someValue]
    /\ fastQuorumVotes' = [fastQuorumVotes EXCEPT ![someValue] = @ + 1]

FastDecision ==
  /\ roundType = "fast"
  /\ \E v \in Values :
    /\ fastQuorumVotes[v] >= Cardinality(Quorums)
    /\ decidedValue' = v
    /\ proposedValues' = {}
    /\ votes' = {}
    /\ fastQuorumVotes' = {}

CollisionRecovery ==
  /\ roundType = "fast"
  /\ \E v \in Values :
    /\ fastQuorumVotes[v] > 0
    /\ fastQuorumVotes[v] < Cardinality(Quorums)
    /\ roundType' = "classic"
    /\ currentRound' = currentRound + 1
    /\ proposedValues' = {}
    /\ votes' = {}

ClassicRoundExecution ==
  /\ roundType = "classic"
  /\ \E v \in Values :
    /\ \E Q \in Quorums :
      /\ \A r \in Q : 
        /\ proposedValues' = [proposedValues EXCEPT ![r] = v]
        /\ votes' = [votes EXCEPT ![r] = v]
        /\ decidedValue' = v
        /\ roundType' = "classic"
        /\ currentRound' = currentRound + 1

Spec ==
  /\ Init
  /\ [][Next]_proposedValues, votes, decidedValue, roundType, currentRound, fastQuorumVotes
  /\ WF_vars(Next)_(proposedValues, votes, decidedValue, roundType, currentRound, fastQuorumVotes)

Agreement ==
  decidedValue # NULL => decidedValue' = decidedValue

NonTriviality ==
  decidedValue # NULL => \E r \in Replicas : proposedValues[r] = decidedValue

Liveness ==
  <>(\E v \in Values : 
    /\ (\E Q \in Quorums : \A r \in Q : proposedValues[r] = v)
    \/ (\E Q \in Quorums : \A r \in Q : votes[r] = v))

THEOREM Spec => []Agreement
THEOREM Spec => []NonTriviality
THEOREM Spec => Liveness

```
Note: The above TLA+ specification models the Fast Paxos consensus protocol as described. However, please note that this is a simplified model and might not cover all edge cases or optimizations of the actual protocol implementation. Additionally, the `WF_vars` (weak fairness) condition ensures that the system makes progress under fair scheduling, which is crucial for liveness properties.