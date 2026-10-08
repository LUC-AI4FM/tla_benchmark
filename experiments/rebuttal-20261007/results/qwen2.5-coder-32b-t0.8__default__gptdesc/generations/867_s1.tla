------------------------------- MODULE Paxos -------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proposers,          \* Set of proposers
    Acceptors,          \* Set of acceptors
    Values              \* Set of possible values

VARIABLES 
    sentPrepare,        \* { <proposer, ballot> } for each sent prepare message
    sentPromise,        \* { <acceptor, proposer, ballot, promiseBallot, promisedValue> } for each sent promise message
    sentAccept,         \* { <proposer, ballot, value> } for each sent accept message
    sentAccepted,       \* { <acceptor, proposer, ballot, acceptedBallot, acceptedValue> } for each sent accepted message
    sentDecide,         \* { <value> } for each sent decide message
    decision,           \* The representative decision value
    highestBallotSeen,  \* { acceptor -> ballot } for the highest ballot seen by each acceptor
    highestBallotAccepted, \* { acceptor -> ballot } for the highest ballot accepted by each acceptor
    acceptedValue       \* { acceptor -> value } for the corresponding accepted value

Init == 
    /\ sentPrepare = {}
    /\ sentPromise = {}
    /\ sentAccept = {}
    /\ sentAccepted = {}
    /\ sentDecide = {}
    /\ decision = <<>>
    /\ highestBallotSeen \in [Acceptors -> 0]
    /\ highestBallotAccepted \in [Acceptors -> 0]
    /\ acceptedValue \in [Acceptors -> <<>>]

Prepare ==
    \/ /\ E(proposer \in Proposers) 
       /\ E(ballot \in Nat)
       /\ ~<<proposer, ballot>> \in sentPrepare
       /\ sentPrepare' = sentPrepare \cup {<<proposer, ballot>>}
       /\ UNCHANGED <<sentPromise, sentAccept, sentAccepted, sentDecide, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>

Promise ==
    \/ /\ E(proposer \in Proposers) 
       /\ E(acceptor \in Acceptors)
       /\ E(ballot \in Nat)
       /\ <<proposer, ballot>> \in sentPrepare
       /\ (highestBallotSeen[acceptor] < ballot)
       /\ (\E promiseBallot \in Nat : promiseBallot <= highestBallotAccepted[acceptor])
       /\ (promiseBallot = 0 => promisedValue = <<>>)
       /\ (promiseBallot > 0 => (\E v \in Values : acceptedValue[acceptor] = v /\ promisedValue = acceptedValue[acceptor]))
       /\ sentPromise' = sentPromise \cup {<<acceptor, proposer, ballot, promiseBallot, promisedValue>>}
       /\ highestBallotSeen' = [highestBallotSeen EXCEPT ![acceptor] = ballot]
       /\ UNCHANGED <<sentPrepare, sentAccept, sentAccepted, sentDecide, decision, highestBallotAccepted, acceptedValue>>

Accept ==
    \/ /\ E(proposer \in Proposers) 
       /\ E(acceptor \in Acceptors)
       /\ E(ballot \in Nat)
       /\ E(value \in Values)
       /\ <<proposer, ballot>> \in sentPrepare
       /\ (\E pmsg \in sentPromise : 
            LET promiseBallot == pmsg[3]
                promisedValue == pmsg[4] 
            IN acceptor = pmsg[0] /\ proposer = pmsg[1] /\ ballot >= promiseBallot)
       /\ sentAccept' = sentAccept \cup {<<proposer, ballot, value>>}
       /\ UNCHANGED <<sentPrepare, sentPromise, sentAccepted, sentDecide, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>

Accepted ==
    \/ /\ E(proposer \in Proposers) 
       /\ E(acceptor \in Acceptors)
       /\ E(ballot \in Nat)
       /\ E(value \in Values)
       /\ <<proposer, ballot, value>> \in sentAccept
       /\ (\A otherBallot \in Nat : 
            (otherBallot < ballot => ~<<acceptor, proposer, otherBallot, _, _>> \in sentAccepted))
       /\ sentAccepted' = sentAccepted \cup {<<acceptor, proposer, ballot, ballot, value>>}
       /\ highestBallotAccepted' = [highestBallotAccepted EXCEPT ![acceptor] = ballot]
       /\ acceptedValue' = [acceptedValue EXCEPT ![acceptor] = value]
       /\ UNCHANGED <<sentPrepare, sentPromise, sentAccept, sentDecide, decision, highestBallotSeen>>

Decide ==
    \/ /\ E(value \in Values)
       /\ (\A a \in Acceptors: value = acceptedValue[a])
       /\ (\E q \subseteq Acceptors : Cardinality(q) > Cardinality(Acceptors) / 2 /\ (\A a \in q : value = acceptedValue[a]))
       /\ decision' = value
       /\ sentDecide' = sentDecide \cup {value}
       /\ UNCHANGED <<sentPrepare, sentPromise, sentAccept, sentAccepted, highestBallotSeen, highestBallotAccepted, acceptedValue>>

Next == 
    Prepare \/ Promise \/ Accept \/ Accepted \/ Decide

Spec ==
    Init /\ [][Next]_<<sentPrepare, sentPromise, sentAccept, sentAccepted, sentDecide, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>

\* Safety properties
TypeOK ==
    /\ sentPrepare \subseteq (Proposers \X Nat)
    /\ sentPromise \subseteq (Acceptors \X Proposers \X Nat \X Nat \X Values)
    /\ sentAccept \subseteq (Proposers \X Nat \X Values)
    /\ sentAccepted \subseteq (Acceptors \X Proposers \X Nat \X Nat \X Values)
    /\ sentDecide \subseteq Values
    /\ decision \in VALUES
    /\ highestBallotSeen \in [Acceptors -> Nat]
    /\ highestBallotAccepted \in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> Values]

NonTriviality ==
    \/ decision = <<>>
    \/ (\E v \in sentAccept : LET proposer == v[0] IN decision = v[2])

Safety == TypeOK /\ NonTriviality

\* Liveness properties
Liveness == FALSE \* Paxos does not guarantee termination under the asynchronous fault model

THEOREM Spec => []Safety

=============================================================================