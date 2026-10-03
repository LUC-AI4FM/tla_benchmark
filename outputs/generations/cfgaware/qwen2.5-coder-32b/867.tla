------------------------------- MODULE PaxosSpec -------------------------------

CONSTANTS 
    \* The set of all proposers
    Proposers,
    
    \* The set of all acceptors
    Acceptors,

    \* The set of all possible values that can be proposed
    Values,

    \* A function from pairs of acceptor sets to a boolean indicating if they form a quorum
    IsQuorum

VARIABLES 
    \* Sent messages: a sequence of tuples (sender, receiver, message_type, ballot_number, value)
    sentMessages,
    
    \* Decision variable: the representative decision value
    decision,

    \* For each acceptor, the highest ballot seen
    highestBallotSeen,
    
    \* For each acceptor, the highest ballot accepted
    highestBallotAccepted,
    
    \* For each acceptor, the corresponding accepted value
    acceptedValue

\* Type invariants for Paxos messages and state variables
PaxosTypeOK == 
    /\ sentMessages \in Seq({<<p, a, mt, bn, v>> \in [Proposers \cup Acceptors -> Proposers \cup Acceptors] \X [Proposers \cup Acceptors -> Proposers \cup Acceptors] \X {"prepare", "promise", "accept", "accepted", "decide"} \X Nat \X (Values \cup {<<>>}) : p \in Proposers \/ a \in Acceptors})
    /\ decision \in Values \cup {<<>>}
    /\ highestBallotSeen \in [Acceptors -> Nat]
    /\ highestBallotAccepted \in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> (Values \cup {<<>>})]

\* Non-triviality safety property: only proposed values can be learned
PaxosNontriviality ==
    \/ decision = <<>>
    \/ \E v \in Values : \A p \in Proposers : \E bn \in Nat : <<p, _, "accept", bn, v>> \in sentMessages

\* Consistency-related temporal property over the decision variable
PaxosConsistency ==
    \A a1, a2 \in Acceptors :
        /\ highestBallotAccepted[a1] = highestBallotAccepted[a2]
        => acceptedValue[a1] = acceptedValue[a2]

Init == 
    /\ sentMessages = << >>
    /\ decision = << >>
    /\ highestBallotSeen = [a \in Acceptors |-> 0]
    /\ highestBallotAccepted = [a \in Acceptors |-> 0]
    /\ acceptedValue = [a \in Acceptors |-> << >>]

Next ==
    \/ \E p \in Proposers, bn \in Nat :
        /\ decision = << >>
        /\ ~(\E m \in sentMessages : m[1] = p /\ m[3] = "prepare" /\ m[4] >= bn)
        /\ sentMessages' = Append(sentMessages, <<p, _, "prepare", bn, << >> >>)
        /\ UNCHANGED <<decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>
    \/ \E p \in Proposers, a \in Acceptors, bn \in Nat :
        /\ decision = << >>
        /\ <<p, a, "prepare", bn, _>> \in sentMessages
        /\ ~(\E m \in sentMessages : m[1] = a /\ m[3] = "promise" /\ m[4] >= highestBallotSeen[a])
        /\ sentMessages' = Append(sentMessages, <<a, p, "promise", highestBallotSeen[a], acceptedValue[a] >>)
        /\ highestBallotSeen' = [highestBallotSeen EXCEPT ![a] = bn]
        /\ UNCHANGED <<decision, highestBallotAccepted, acceptedValue>>
    \/ \E p \in Proposers, a \in Acceptors, bn \in Nat, v \in Values :
        /\ decision = << >>
        /\ <<p, a, "promise", bn, _>> \in sentMessages
        /\ ~(\E m \in sentMessages : m[1] = p /\ m[3] = "accept" /\ m[4] >= bn)
        /\ sentMessages' = Append(sentMessages, <<p, a, "accept", bn, v >>)
        /\ UNCHANGED <<decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>
    \/ \E p \in Proposers, a \in Acceptors, bn \in Nat, v \in Values :
        /\ decision = << >>
        /\ <<p, a, "accept", bn, v>> \in sentMessages
        /\ ~(\E m \in sentMessages : m[1] = a /\ m[3] = "accepted" /\ m[4] >= highestBallotAccepted[a])
        /\ sentMessages' = Append(sentMessages, <<a, p, "accepted", bn, v >>)
        /\ highestBallotAccepted' = [highestBallotAccepted EXCEPT ![a] = bn]
        /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
        /\ UNCHANGED <<decision, highestBallotSeen>>
    \/ \E p \in Proposers, a \in Acceptors, bn \in Nat, v \in Values :
        /\ decision = << >>
        /\ IsQuorum({a' \in Acceptors : highestBallotAccepted[a'] >= bn})
        /\ \A a' \in {a' \in Acceptors : highestBallotAccepted[a'] >= bn} : acceptedValue[a'] = v
        /\ sentMessages' = Append(sentMessages, <<p, _, "decide", bn, v >>)
        /\ decision' = v
        /\ UNCHANGED <<highestBallotSeen, highestBallotAccepted, acceptedValue>>

Spec == Init /\ [][Next]_<<sentMessages, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>

\* Liveness is explicitly set to FALSE as Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning
LIVENESS == FALSE

=============================================================================