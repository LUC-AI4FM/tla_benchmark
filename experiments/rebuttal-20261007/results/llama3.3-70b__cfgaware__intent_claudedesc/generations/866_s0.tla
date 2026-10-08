--------------------------- MODULE FastPaxos ---------------------------
EXTENDS Integers, TLC

CONSTANTS Replicas, Values, Coordinator, FastQuorums, ClassicQuorums
VARIABLES proposedValues, votes, decidedValue, roundType, currentRound

TypeOK == /\ proposedValues \in [Replicas -> Values \cup {<<>>}]
          /\ votes \in [Replicas -> Values \cup {<<>>}]
          /\ decidedValue \in Values \cup {<<>>}
          /\ roundType \in {"fast", "classic"}
          /\ currentRound \in Nat

FastTypeOK == TypeOK

Init == /\ proposedValues = [r \in Replicas |-> <<>>]
        /\ votes = [r \in Replicas |-> <<>>]
        /\ decidedValue = <<
        /\ roundType = "fast"
        /\ currentRound = 0

Next == \/ FastRoundNext
         \/ ClassicRoundNext
         \/ CollisionRecoveryNext

FastRoundNext == /\ roundType = "fast"
                 /\ currentRound' = currentRound + 1
                 /\ proposedValues' = [proposedValues EXCEPT ![r \in Replicas |-> IF votes[r] = <<>> THEN someValue(r) ELSE votes[r]]]
                 /\ votes' = [votes EXCEPT ![r \in Replicas |-> proposedValues'[r]]]
                 /\ decidedValue' = IF FastDecisionCondition(proposedValues', votes') THEN SomeValue(votes') ELSE decidedValue
                 /\ roundType' = IF decidedValue' /= <<>> THEN "classic" ELSE "fast"

ClassicRoundNext == /\ roundType = "classic"
                    /\ currentRound' = currentRound + 1
                    /\ proposedValues' = [proposedValues EXCEPT ![r \in Replicas |-> someValue(r)]]
                    /\ votes' = [votes EXCEPT ![r \in Replicas |-> proposedValues'[r]]]
                    /\ decidedValue' = IF ClassicDecisionCondition(votes') THEN SomeValue(votes') ELSE decidedValue
                    /\ roundType' = "classic"

CollisionRecoveryNext == /\ roundType = "fast"
                         /\ currentRound' = currentRound + 1
                         /\ proposedValues' = [proposedValues EXCEPT ![r \in Replicas |-> someValue(r)]]
                         /\ votes' = [votes EXCEPT ![r \in Replicas |-> proposedValues'[r]]]
                         /\ decidedValue' = IF CollisionRecoveryCondition(votes') THEN SomeValue(votes') ELSE decidedValue
                         /\ roundType' = "classic"

FastDecisionCondition(proposedValues, votes) == \E v \in Values : \A r \in someFastQuorum : proposedValues[r] = v /\ votes[r] = v

ClassicDecisionCondition(votes) == \E v \in Values : \A r \in someClassicQuorum : votes[r] = v

CollisionRecoveryCondition(votes) == \E v \in Values : \A r \in someFastQuorum : votes[r] = v

SomeValue(values) == CHOOSE v \in Values : v \in values

someFastQuorum == CHOOSE fq \in FastQuorums : TRUE
someClassicQuorum == CHOOSE cq \in ClassicQuorums : TRUE

someValue(r) == CHOOSE v \in Values : TRUE

PaxosConsistency == /\ Agreement
                     /\ Nontriviality
                     /\ Liveness

Agreement == decidedValue \in [decidedValue] \cup {<<>>}

Nontriviality == decidedValue \in proposedValues

Liveness == <>(decidedValue /= <<>>)

FastSpec == Spec(Init, Next) /\ PaxosConsistency

FastNontriviality == Nontriviality
=============================================================================