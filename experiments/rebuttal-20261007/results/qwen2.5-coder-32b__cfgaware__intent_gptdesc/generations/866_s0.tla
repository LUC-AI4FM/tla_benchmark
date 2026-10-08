------------------------------- MODULE FastPaxos -------------------------------

CONSTANTS 
    Replicas,          \* Set of all replicas (proposers, acceptors, coordinator)
    FastQuorums,       \* Set of fast quorum sets
    ClassicQuorums     \* Set of classic quorum sets

ASSUME 
    /\ Replicas = UNION FastQuorums
    /\ Replicas = UNION ClassicQuorums
    /\ \A Q1 \in FastQuorums, Q2 \in FastQuorums: Q1 \cap Q2 # {}
    /\ \A Q \in FastQuorums, C \in ClassicQuorums: Q \cap C # {}

VARIABLES 
    proposedValues,     \* Proposed values per replica
    fastResponses,      \* Responses from acceptors in a fast round
    classicValue,       \* Value chosen by the coordinator for a classic round
    acceptedValues      \* Accepted values per replica

INSTANCE Naturals AS Nat

FastSpec == 
    /\ proposedValues \in [Replicas -> [Nat -> {FALSE} \cup (UNION {[v] : v \in Replicas})]]
    /\ fastResponses \in [Replicas -> [Nat -> [Replicas -> {FALSE} \cup (UNION {[v] : v \in Replicas})]]]
    /\ classicValue \in [Nat -> {FALSE} \cup (UNION {[v] : v \in Replicas})]
    /\ acceptedValues \in [Replicas -> [Nat -> {FALSE} \cup (UNION {[v] : v \in Replicas})]]

FastTypeOK ==
    /\ proposedValues \subseteq [Replicas -> [Nat -> {FALSE} \cup Replicas]]
    /\ fastResponses \subseteq [Replicas -> [Nat -> [Replicas -> {FALSE} \cup Replicas]]]
    /\ classicValue \subseteq [Nat -> {FALSE} \cup Replicas]
    /\ acceptedValues \subseteq [Replicas -> [Nat -> {FALSE} \cup Replicas]]

FastNontriviality ==
    \A i \in Nat, v \in acceptedValues[Replica][i] : 
        \E r \in Replicas : proposedValues[r][i] = v

PaxosConsistency ==
    /\ Agreement
    /\ FastNontriviality
    /\ ValidConflictResolution

Agreement ==
    \A i \in Nat, v1, v2 \in acceptedValues[Replica][i] :
        v1 = v2

ValidConflictResolution ==
    \A i \in Nat : 
        LET fastQuorumResponses == {v \in Replicas : \E Q \in FastQuorums : (\A r \in Q : fastResponses[r][i] = v)}
            majorityValue == CHOOSE v \in fastQuorumResponses : Cardinality({r \in Replicas : fastResponses[r][i] = v}) > Cardinality(Q) / 2
        IN 
        \/ classicValue[i] = FALSE
        \/ (\E v \in fastQuorumResponses : Cardinality({r \in Replicas : fastResponses[r][i] = v}) > Cardinality(Q) / 2 /\ classicValue[i] = majorityValue)
        \/ classicValue[i] \in fastQuorumResponses

Init ==
    /\ proposedValues = [r \in Replicas -> [i \in Nat -> FALSE]]
    /\ fastResponses = [r \in Replicas -> [i \in Nat -> [a \in Replicas -> FALSE]]]
    /\ classicValue = [i \in Nat -> FALSE]
    /\ acceptedValues = [r \in Replicas -> [i \in Nat -> FALSE]]

Next ==
    \/ \E r \in Replicas, i \in Nat, v \in Replicas : 
        proposedValues' = [proposedValues EXCEPT ![r][i] = v]
    \/ \E r \in Replicas, a \in Replicas, i \in Nat, v \in Replicas :
        fastResponses' = [fastResponses EXCEPT ![r][i][a] = v]
    \/ \E i \in Nat, v \in Replicas : 
        classicValue' = [classicValue EXCEPT ![i] = v]
    \/ \E r \in Replicas, i \in Nat, v \in Replicas :
        acceptedValues' = [acceptedValues EXCEPT ![r][i] = v]

Spec ==
    Init /\ [][Next]_<<proposedValues, fastResponses, classicValue, acceptedValues>>

Fairness ==
    WF_next(Next)

THEOREM Spec => []PaxosConsistency

=============================================================================