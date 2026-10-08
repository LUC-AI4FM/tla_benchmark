---------------------------- MODULE PaxosSpec ----------------------------

CONSTANTS 
    \* The set of all proposers
    Proposers,
    
    \* The set of all acceptors
    Acceptors,

    \* The set of all possible values that can be proposed
    Values,

    \* A function from pairs of subsets of Acceptors to BOOLEAN, indicating whether the two sets have a quorum intersection
    Quorum

VARIABLES 
    \* Ballot numbers issued by proposers (proposer -> ballot number)
    Ballots,
    
    \* The highest ballot number promised by each acceptor (acceptor -> ballot number)
    PromisedBallots,
    
    \* The highest accepted ballot and value for each acceptor (acceptor -> [ballot: _, value: _])
    AcceptedBallots

\* Message types
TYPEDEF Msg == <<proposer: Proposers, ballot: Ballots[proposer], type: {"Prepare", "Promise", "Accept", "Accepted"}, data: [ballot: Ballots[proposer] -> Values UNION {}]>>

\* Initial state predicate
Init == 
    /\ Ballots \in [Proposers -> Nat]
    /\ PromisedBallots \in [Acceptors -> 0]
    /\ AcceptedBallots \in [Acceptors -> [ballot: 0, value: <<>>]]

\* Next-state relation for proposer actions
NextProposer ==
    \/ \E p \in Proposers, b \in Nat:
        /\ Ballots' = [Ballots EXCEPT ![p] = b]
        /\ PromisedBallots' = PromisedBallots
        /\ AcceptedBallots' = AcceptedBallots
        /\ UNCHANGED <<proposer, ballot, type, data>>
    \/ \E p \in Proposers, b \in Ballots[p], q \in Acceptors:
        /\ \A a \in Acceptors: 
            \/ PromisedBallots[a] < b
            \/ (PromisedBallots[a] = b /\ AcceptedBallots[a].ballot < b)
        /\ UNCHANGED <<proposer, ballot, type, data>>
    \/ \E p \in Proposers, b \in Ballots[p], q \in Acceptors:
        /\ \A a \in Acceptors: 
            \/ PromisedBallots[a] < b
            \/ (PromisedBallots[a] = b /\ AcceptedBallots[a].ballot < b)
        /\ UNCHANGED <<proposer, ballot, type, data>>

\* Next-state relation for acceptor actions
NextAcceptor ==
    \/ \E a \in Acceptors, m \in Msg:
        /\ m.type = "Prepare"
        /\ PromisedBallots' = [PromisedBallots EXCEPT ![a] = Max(PromisedBallots[a], m.ballot)]
        /\ AcceptedBallots' = AcceptedBallots
        /\ UNCHANGED <<proposer, ballot, type, data>>
    \/ \E a \in Acceptors, m \in Msg:
        /\ m.type = "Accept"
        /\ PromisedBallots'[a] = PromisedBallots[a]
        /\ (PromisedBallots[a] < m.ballot) 
            -> AcceptedBallots' = [AcceptedBallots EXCEPT ![a] = [ballot |-> m.ballot, value |-> m.data[m.ballot]]]
        /\ (PromisedBallots[a] >= m.ballot)
            -> AcceptedBallots' = AcceptedBallots
        /\ UNCHANGED <<proposer, ballot, type, data>>

\* Next-state relation for message delivery
NextMessage ==
    \/ \E a \in Acceptors, p \in Proposers, b \in Ballots[p]:
        /\ PromisedBallots'[a] = Max(PromisedBallots[a], b)
        /\ AcceptedBallots' = AcceptedBallots
        /\ UNCHANGED <<proposer, ballot, type, data>>
    \/ \E a \in Acceptors, p \in Proposers, b \in Ballots[p]:
        /\ PromisedBallots'[a] = Max(PromisedBallots[a], b)
        /\ AcceptedBallots' = [AcceptedBallots EXCEPT ![a] = [ballot |-> b, value |-> <<>>]]
        /\ UNCHANGED <<proposer, ballot, type, data>>

\* Full next-state relation
Next == NextProposer \/ NextAcceptor \/ NextMessage

\* Type-correctness invariant
PaxosTypeOK ==
    /\ Ballots \in [Proposers -> Nat]
    /\ PromisedBallots \in [Acceptors -> Nat]
    /\ AcceptedBallots \in [Acceptors -> [ballot: Nat, value: Values UNION {}]]

\* Validity invariant (nontriviality)
PaxosNontriviality ==
    \A a \in Acceptors:
        \/ AcceptedBallots[a].value = <<>>
        \/ \E p \in Proposers: 
            /\ Ballots[p] = AcceptedBallots[a].ballot
            /\ Values \in [AcceptedBallots[a].value]

\* Consistency invariant (safety)
PaxosConsistency ==
    \A a, b \in Acceptors:
        \/ AcceptedBallots[a].ballot # AcceptedBallots[b].ballot
        \/ AcceptedBallots[a].value = AcceptedBallots[b].value

\* Quorum intersection invariant
QuorumIntersection ==
    \A S1, S2 \subseteq Acceptors: 
        Quorum[S1, S2] => /\ S1 \cap S2 # {}
                         /\ Cardinality(S1 \cup S2) > Cardinality(Acceptors) / 2

\* Specification formula
Spec == Init /\ [][Next]_<<proposer, ballot, type, data>>

=============================================================================