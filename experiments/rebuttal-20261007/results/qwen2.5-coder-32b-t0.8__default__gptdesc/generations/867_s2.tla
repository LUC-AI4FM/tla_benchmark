------------------------------ MODULE Paxos ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proposers, Acceptors, Values, Ballots

VARIABLES 
    sentMessages,  \* Set of messages sent: <<type, ballot, proposer/acceptor, value>>
    decision,      \* Representative decision value
    acceptorState  \* Mapping from acceptor to record {highestSeenBallot, highestAcceptedBallot, acceptedValue}

Init == 
    /\ sentMessages = {}
    /\ decision = <<>>
    /\ (\A a \in Acceptors: acceptorState[a] = [highestSeenBallot |-> <<>>, highestAcceptedBallot |-> <<>>, acceptedValue |-> <<>>])

Next ==
    \/ \E p \in Proposers, b \in Ballots, v \in Values:
        /\ sentMessages' = sentMessages \cup {<< "prepare", b, p >>}
        /\ UNCHANGED <<decision, acceptorState>>
    \/ \E a \in Acceptors, m \in sentMessages, b1 \in Ballots:
        /\ m = << "prepare", b1, _ >>
        /\ LET b2 == acceptorState[a].highestSeenBallot
           v  == IF b2 = <<>> THEN <<>> ELSE acceptorState[a].acceptedValue
        IN
        /\ sentMessages' = sentMessages \cup {<< "promise", b2, a, b1, v >>}
        /\ UNCHANGED <<decision, acceptorState>>
    \/ \E p \in Proposers, m \in sentMessages, b1 \in Ballots, v \in Values:
        /\ m = << "promise", _, a, b1, _ >>
        /\ LET promises == {m' \in sentMessages: m' = << "promise", _, a, b1, _ >>}
           quorum   == Cardinality(promises) > Cardinality(Acceptors) / 2
        IN
        /\ quorum
        /\ sentMessages' = sentMessages \cup {<< "accept", b1, p, v >>}
        /\ UNCHANGED <<decision, acceptorState>>
    \/ \E a \in Acceptors, m \in sentMessages, b1 \in Ballots, v \in Values:
        /\ m = << "accept", b1, p, v >>
        /\ LET b2 == acceptorState[a].highestSeenBallot
        IN
        /\ b1 >= b2
        /\ sentMessages' = sentMessages \cup {<< "accepted", a, b1 >>}
        /\ acceptorState' = [acceptorState EXCEPT ![a] = 
            <<highestSeenBallot |-> b1, highestAcceptedBallot |-> b1, acceptedValue |-> v>>]
        /\ UNCHANGED decision
    \/ \E p \in Proposers, m \in sentMessages:
        /\ m = << "accepted", _, _ >>
        /\ LET accepteds == {m' \in sentMessages: m' = << "accepted", _, _ >>}
           quorum    == Cardinality(accepteds) > Cardinality(Acceptors) / 2
        IN
        /\ quorum
        /\ decision' = Head({v : <<_, b, p, v>> \in sentMessages})
        /\ UNCHANGED acceptorState

Spec ==
    /\ Init
    /\ [][Next]_<<sentMessages, decision, acceptorState>>
    /\ WF_next(<<sentMessages, decision, acceptorState>>)

\* Safety properties
TypeOK == 
    /\ (\A m \in sentMessages: 
        \/ (m[1] = "prepare" /\ Len(m) = 4)
        \/ (m[1] = "promise" /\ Len(m) = 6)
        \/ (m[1] = "accept"  /\ Len(m) = 5)
        \/ (m[1] = "accepted" /\ Len(m) = 3))
    /\ decision \in Values \/ decision = <<>>
    /\ (\A a \in Acceptors: 
        LET s == acceptorState[a]
        IN
        /\ s.highestSeenBallot \in Ballots \/ s.highestSeenBallot = <<>>
        /\ s.highestAcceptedBallot \in Ballots \/ s.highestAcceptedBallot = <<>>
        /\ (s.highestAcceptedBallot = <<>> => s.acceptedValue = <<>>)
        /\ (s.highestAcceptedBallot /= <<>> => s.acceptedValue \in Values))

NonTriviality ==
    /\ decision = <<>> \/ (\E p \in Proposers, b \in Ballots, v \in Values:
        LET prepares == {m \in sentMessages: m[1] = "prepare" /\ m[2] = b}
            accepts  == {m \in sentMessages: m[1] = "accept"  /\ m[2] = b /\ m[4] = v}
            quorum   == Cardinality(accepts) > Cardinality(Acceptors) / 2
        IN
        /\ Len(prepares) >= 1 
        /\ quorum)

Consistency ==
    /\ decision = <<>> \/ (\A a \in Acceptors: 
        LET s == acceptorState[a]
        IN
        (decision = <<>> => s.acceptedValue = <<>>) 
        \/ decision = s.acceptedValue)

\* Liveness property is explicitly set to FALSE
Liveness ==
    FALSE

=============================================================================