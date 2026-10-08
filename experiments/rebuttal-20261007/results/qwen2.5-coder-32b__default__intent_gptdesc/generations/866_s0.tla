------------------------------- MODULE FastPaxos -------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Replicas,          \* Set of all replicas (proposers, acceptors, coordinators)
    FastQuorums,       \* Set of fast quorum sets
    ClassicQuorums     \* Set of classic quorum sets

VARIABLES 
    proposedValues,    \* Proposed values per replica
    acceptedValues,    \* Accepted values per replica
    decidedValue,      \* Decided value for the instance
    roundType          \* Type of current round: "fast" or "classic"

ASSUME 
    /\ Replicas \subseteq (Replicas \cup FastQuorums \cup ClassicQuorums)
    /\ \A q1, q2 \in FastQuorums : q1 \cap q2 # {}
    /\ \A q \in FastQuorums, cq \in ClassicQuorums : q \cap cq # {}

Init == 
    /\ proposedValues = [r \in Replicas |-> {}]
    /\ acceptedValues = [r \in Replicas |-> {}]
    /\ decidedValue = <<>>
    /\ roundType = "fast"

Next ==
    \/ \* Fast Round: Proposer signals a value
       (\E r \in Replicas, v \in (Replicas -> BOOLEAN) :
            /\ proposedValues' = [proposedValues EXCEPT ![r] = proposedValues[r] \cup {v}]
            /\ acceptedValues' = acceptedValues
            /\ decidedValue' = decidedValue
            /\ roundType' = "fast"
       )
    \/ \* Fast Round: Acceptor responds with current value
       (\E r1, r2 \in Replicas :
            /\ proposedValues'[r1] = proposedValues[r1]
            /\ acceptedValues' = [acceptedValues EXCEPT ![r2] = acceptedValues[r2] \cup (IF decidedValue # <<>> THEN {decidedValue} ELSE proposedValues[r1])]
            /\ decidedValue' = decidedValue
            /\ roundType' = "fast"
       )
    \/ \* Fast Round: Decide value if fast quorum agrees on a single value
       (\E q \in FastQuorums, v :
            /\ \A r \in q : v \in acceptedValues[r]
            /\ proposedValues' = proposedValues
            /\ acceptedValues' = acceptedValues
            /\ decidedValue' = v
            /\ roundType' = "fast"
       )
    \/ \* Classic Round: Coordinator chooses a value based on fast quorum responses
       (\E c \in Replicas, q \in FastQuorums :
            LET values = UNION {acceptedValues[r] : r \in q}
                majorityValue = CHOOSE v \in values : Cardinality({r \in q : v \in acceptedValues[r]}) > Cardinality(q) / 2
                chosenValue = IF majorityValue # <<>> THEN majorityValue ELSE (CHOOSE v \in values : TRUE)
            IN
                /\ proposedValues' = [proposedValues EXCEPT ![c] = {chosenValue}]
                /\ acceptedValues' = acceptedValues
                /\ decidedValue' = decidedValue
                /\ roundType' = "classic"
       )
    \/ \* Classic Round: Acceptor accepts the chosen value
       (\E r1, r2 \in Replicas :
            /\ proposedValues'[r1] = proposedValues[r1]
            /\ acceptedValues' = [acceptedValues EXCEPT ![r2] = acceptedValues[r2] \cup {proposedValues[r1][r1]}]
            /\ decidedValue' = decidedValue
            /\ roundType' = "classic"
       )
    \/ \* Classic Round: Decide value if classic quorum accepts the same value
       (\E q \in ClassicQuorums, v :
            /\ \A r \in q : v \in acceptedValues[r]
            /\ proposedValues' = proposedValues
            /\ acceptedValues' = acceptedValues
            /\ decidedValue' = v
            /\ roundType' = "classic"
       )

Spec ==
    WF_vars(Next) /\
    Init /\ [][Next]_<<proposedValues, acceptedValues, decidedValue, roundType>> /\
    \A v1, v2 : <<v1>> \in decidedValue => v1 = v2 /\
    \A v : <<v>> \in decidedValue => \E r \in Replicas : v \in proposedValues[r] /\
    \A q \in FastQuorums, values = UNION {acceptedValues[r] : r \in q} :
        LET majorityValue = CHOOSE v \in values : Cardinality({r \in q : v \in acceptedValues[r]}) > Cardinality(q) / 2
            chosenValue = IF majorityValue # <<>> THEN majorityValue ELSE (CHOOSE v \in values : TRUE)
        IN
            \A c \in Replicas : proposedValues[c] = {chosenValue} => decidedValue = chosenValue

=============================================================================