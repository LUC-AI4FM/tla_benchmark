------------------------------- MODULE FastPaxos -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Replicas,          \* Set of all replicas (acceptors)
    Coordinator,       \* The unique coordinator
    Values             \* Set of possible values to be agreed upon

VARIABLES 
    fastBallotNumber,  \* Ballot number for the current fast round
    classicBallotNumber,\* Ballot number for the current classic round
    proposals,         \* Mapping from replicas to proposed values in a fast round
    votes,             \* Votes cast by replicas in a fast or classic round
    decidedValue       \* The value that has been decided

ASSUME 
    Cardinality(Replicas) >= 4 /\ Coordinator \notin Replicas
    LET q == (Cardinality(Replicas) * 3) \div 4 IN
        \A Q1, Q2 \in SUBSET Replicas : Q1 \subseteq Replicas /\ Q2 \subseteq Replicas /\ Cardinality(Q1) >= q /\ Cardinality(Q2) >= q => Q1 \cap Q2 /= {}
    LET q == (Cardinality(Replicas) * 3) \div 4 IN
        \A Qf, Qc \in SUBSET Replicas : Qf \subseteq Replicas /\ Qc \subseteq Replicas /\ Cardinality(Qf) >= q => Qf \cap Qc /= {}

Init == 
    /\ fastBallotNumber = 0
    /\ classicBallotNumber = 0
    /\ proposals = [r \in Replicas |-> <<>>]
    /\ votes = [b \in {fastBallotNumber, classicBallotNumber} |-> [r \in Replicas |-> <<>>]]
    /\ decidedValue = <<>>

Next == 
    \/ FastRoundInitiation
    \/ FastVoting
    \/ FastDecision
    \/ CollisionRecovery
    \/ ClassicRoundExecution

FastRoundInitiation ==
    /\ fastBallotNumber' = fastBallotNumber + 1
    /\ classicBallotNumber' = classicBallotNumber
    /\ proposals' = [proposals EXCEPT ![r] = <<>> \forall r \in Replicas]
    /\ votes' = [votes EXCEPT ![fastBallotNumber'] = [r \in Replicas |-> <<>>]]
    /\ decidedValue' = decidedValue

FastVoting ==
    \E r \in Replicas, v \in Values :
        /\ proposals[r] = <<>>
        /\ proposals' = [proposals EXCEPT ![r] = v]
        /\ votes[fastBallotNumber][r] = <<>>
        /\ votes' = [votes EXCEPT ![fastBallotNumber][r] = v]
        /\ fastBallotNumber' = fastBallotNumber
        /\ classicBallotNumber' = classicBallotNumber
        /\ decidedValue' = decidedValue

FastDecision ==
    LET q == (Cardinality(Replicas) * 3) \div 4 IN
    \E v \in Values :
        /\ Cardinality({r \in Replicas : votes[fastBallotNumber][r] = v}) >= q
        /\ fastBallotNumber' = fastBallotNumber
        /\ classicBallotNumber' = classicBallotNumber
        /\ proposals' = proposals
        /\ votes' = votes
        /\ decidedValue' = v

CollisionRecovery ==
    LET q == (Cardinality(Replicas) * 3) \div 4 IN
    \/ \E v \in Values :
        /\ Cardinality({r \in Replicas : votes[fastBallotNumber][r] = v}) >= q
        /\ classicBallotNumber' = classicBallotNumber + 1
        /\ fastBallotNumber' = fastBallotNumber
        /\ proposals' = [proposals EXCEPT ![r] = <<>> \forall r \in Replicas]
        /\ votes' = [votes EXCEPT ![classicBallotNumber'] = [r \in Replicas |-> <<>>]]
        /\ decidedValue' = decidedValue
    \/ classicBallotNumber' = classicBallotNumber + 1
       /\ fastBallotNumber' = fastBallotNumber
       /\ proposals' = [proposals EXCEPT ![r] = <<>> \forall r \in Replicas]
       /\ votes' = [votes EXCEPT ![classicBallotNumber'] = [r \in Replicas |-> <<>>]]
       /\ decidedValue' = decidedValue

ClassicRoundExecution ==
    LET q == (Cardinality(Replicas) * 3) \div 4 IN
    \/ \E v \in Values :
        /\ Cardinality({r \in Replicas : votes[classicBallotNumber][r] = v}) >= q
        /\ classicBallotNumber' = classicBallotNumber
        /\ fastBallotNumber' = fastBallotNumber
        /\ proposals' = proposals
        /\ votes' = votes
        /\ decidedValue' = v
    \/ \E r \in Replicas, v \in Values :
        /\ votes[classicBallotNumber][r] = <<>>
        /\ votes' = [votes EXCEPT ![classicBallotNumber][r] = v]
        /\ classicBallotNumber' = classicBallotNumber
        /\ fastBallotNumber' = fastBallotNumber
        /\ proposals' = proposals
        /\ decidedValue' = decidedValue

Spec == 
    Init /\ [][Next]_<<fastBallotNumber, classicBallotNumber, proposals, votes, decidedValue>>

Agreement ==
    \A v1, v2 \in Values : decidedValue = v1 => decidedValue = v2

Validity ==
    \/ decidedValue = <<>>
    \/ \E r \in Replicas : \E b \in {fastBallotNumber} : proposals[r] = decidedValue /\ votes[b][r] = decidedValue

Liveness ==
    WF_next(<<fastBallotNumber, classicBallotNumber, proposals, votes, decidedValue>>)

THEOREM Spec => []Agreement
THEOREM Spec => []Validity
THEOREM Spec => <>[]Liveness
=============================================================================