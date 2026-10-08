------------------------------ MODULE FastPaxos ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    \* Number of participants (excluding the coordinator)
    N,
    \* Quorum size
    Q,
    \* Set of all values that can be proposed
    Values
    
VARIABLES 
    \* Current round number
    round,
    \* Proposal for each round
    proposal,
    \* Decided value
    decidedValue,
    \* Votes received in the current round (value -> set of participants)
    votes

ASSUME Q > N / 2 /\ N \in Nat

Init == 
    /\ round = 0
    /\ proposal = [r \in 1..N+1 |-> <<FALSE, "">>]  
    /\ decidedValue = ""
    /\ votes = [v \in Values |-> {}]

Next ==
    \/ /\ \/ \E v \in Values : 
            /\ proposal[round] = <<FALSE, "">>
            /\ proposal' = [proposal EXCEPT ![round] = <<TRUE, v>>]
       /\ round' = round
       /\ votes' = votes
       /\ decidedValue' = decidedValue
    \/ /\ \/ proposal[round][1]
           /\ \E p \in 1..N : 
                /\ p \notin votes[proposal[round][2]]
                /\ votes' = [votes EXCEPT ![proposal[round][2]] = votes[proposal[round][2]] \cup {p}]
       /\ round' = round
       /\ proposal' = proposal
       /\ decidedValue' = decidedValue
    \/ /\ \/ \A v \in Values : Cardinality(votes[v]) >= Q
           /\ \E v1, v2 \in Values : 
                /\ v1 /= v2 
                /\ Cardinality(votes[v1] \cap votes[v2]) < Q
           /\ decidedValue' = CHOOSE v \in Values : Cardinality(votes[v]) >= Q
       /\ round' = round + 1
       /\ proposal' = [proposal EXCEPT ![round'] = <<FALSE, "">>]
       /\ votes' = [v \in Values |-> {}]

Spec == 
    /\ Init
    /\ [][Next]_<<round, proposal, decidedValue, votes>>
    /\ WF_next(<<round, proposal, decidedValue, votes>>, Next)

\* Safety invariants
TypeOK ==
    /\ round \in 1..N+1
    /\ \A r \in 1..N+1 : \/ proposal[r] = <<FALSE, "">> 
                             \/ \E v \in Values : proposal[r] = <<TRUE, v>>
    /\ decidedValue \in Values \/ decidedValue = ""
    /\ \A v \in Values : votes[v] \subseteq (1..N)

DecidedValueProposed ==
    \/ decidedValue = ""
    \/ \E r \in 1..N+1 :
        proposal[r] = <<TRUE, decidedValue>>

\* Liveness properties
Termination ==
    <>(decidedValue /= "")

====