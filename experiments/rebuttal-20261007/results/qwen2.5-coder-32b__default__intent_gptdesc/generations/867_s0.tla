------------------------------- MODULE Paxos -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proposers, Acceptors, QuorumSize

VARIABLES 
    ballotNumber, proposedValue, promisedBallot, acceptedBallot, acceptedValue, messages

Init == /\ ballotNumber = <<>>
          /\ proposedValue = [p \in Proposers |>>]
          /\ promisedBallot = [a \in Acceptors |>>]
          /\ acceptedBallot = [a \in Acceptors |>>]
          /\ acceptedValue = [a \in Acceptors |>>]
          /\ messages = {}

Prepare(p, bn) == <<p, "prepare", bn>>

Promise(a, p, bn, abn, av) == <<a, "promise", p, bn, abn, av>>

Accept(p, bn, v) == <<p, "accept", bn, v>>

Accepted(a, p, bn, v) == <<a, "accepted", p, bn, v>>

Decide(v) == <<v, "decide">>

TypeOK ==
    /\ \A m \in messages: 
        \/ \E p \in Proposers, bn \in Nat: m = Prepare(p, bn)
        \/ \E a \in Acceptors, p \in Proposers, bn, abn \in Nat, av \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]: m = Promise(a, p, bn, abn, av)
        \/ \E p \in Proposers, bn \in Nat, v \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]: m = Accept(p, bn, v)
        \/ \E a \in Acceptors, p \in Proposers, bn \in Nat, v \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]: m = Accepted(a, p, bn, v)

QuorumIntersection ==
    /\ QuorumSize > 1
    /\ QuorumSize <= Cardinality(Acceptors)
    /\ \A Q1, Q2 \in SUBSET Acceptors: 
        Cardinality(Q1) >= QuorumSize /\ Cardinality(Q2) >= QuorumSize
        => Cardinality(Q1 \cap Q2) > 0

Monotonicity ==
    /\ \A a \in Acceptors:
        \/ promisedBallot'[a] = promisedBallot[a]
        \/ /\ promisedBallot'[a] /= promisedBallot[a]
           /\ \E m \in messages: 
                \/ /\ m[1] = a
                   /\ m[2] = "promise"
                   /\ m[3] \in Proposers
                   /\ m[4] = promisedBallot'[a]
                   /\ m[5] <= acceptedBallot[a]
                   /\ (m[6] = acceptedValue[a] \/ acceptedValue[a] = <<>>)
                \/ /\ m[1] = a
                   /\ m[2] = "accepted"
                   /\ m[3] \in Proposers
                   /\ m[4] >= promisedBallot'[a]
    /\ \A a \in Acceptors:
        \/ acceptedBallot'[a] = acceptedBallot[a]
        \/ /\ acceptedBallot'[a] /= acceptedBallot[a]
           /\ \E m \in messages: 
                m[1] = a
                /\ m[2] = "accepted"
                /\ m[3] \in Proposers
                /\ m[4] >= promisedBallot'[a]

Safety ==
    \/ \A v1, v2 \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]: 
        \/ v1 = v2
        \/ ~(\E a1, a2 \in Acceptors: acceptedValue[a1] = v1 /\ acceptedValue[a2] = v2)

Validity ==
    \A v \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]: 
        \/ v = <<>>
        \/ \E p \in Proposers: proposedValue[p] = v

Next ==
    \/ \E p \in Proposers, bn \in Nat:
        /\ ballotNumber' = Append(ballotNumber, <<p, bn>>)
        /\ proposedValue' = [proposedValue EXCEPT ![p] = <<bn, proposedValue[p][2]>>]
        /\ messages' = messages \cup {Prepare(p, bn)}
    \/ \E a \in Acceptors, p \in Proposers, bn, abn \in Nat, av \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]:
        /\ \E m \in messages: m = Prepare(p, bn)
        /\ bn >= promisedBallot[a]
        /\ (abn = acceptedBallot[a] \/ acceptedBallot[a] = <<>>)
        /\ (av = acceptedValue[a] \/ acceptedValue[a] = <<>>)
        /\ promisedBallot'[a] = bn
        /\ messages' = messages \cup {Promise(a, p, bn, abn, av)}
    \/ \E p \in Proposers, bn \in Nat, v \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]:
        /\ \A a \in Acceptors: 
            \/ promisedBallot[a] = <<>>
            \/ bn >= promisedBallot[a]
        /\ messages' = messages \cup {Accept(p, bn, v)}
    \/ \E a \in Acceptors, p \in Proposers, bn \in Nat, v \in [UNION {S : S \in SUBSET (DOMAIN proposedValue)}]:
        /\ \E m \in messages: m = Accept(p, bn, v)
        /\ bn >= promisedBallot[a]
        /\ (acceptedBallot[a] = <<>> \/ acceptedBallot[a] <= bn)
        /\ acceptedBallot'[a] = bn
        /\ acceptedValue'[a] = v
        /\ messages' = messages \cup {Accepted(a, p, bn, v)}

Spec ==
    Init /\ [][Next]_<<ballotNumber, proposedValue, promisedBallot, acceptedBallot, acceptedValue, messages>> /\ WF_next(<<ballotNumber, proposedValue, promisedBallot, acceptedBallot, acceptedValue, messages>>)

INVARSPEC 
    TypeOK
    /\ QuorumIntersection
    /\ Monotonicity
    /\ Safety
    /\ Validity

=============================================================================